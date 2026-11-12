//! Values and calls cargo-mutants can replace without a ciphertext check
//! noticing: `Debug`, `PartialEq`, lengths, errors, and the seal/open shapes
//! the round-trip tests do not call. Compared with aws-lc-rs where the two
//! still agree.
//!
//! aws-lc-rs prints a different `Debug` for an HKDF salt and PRK (it names the
//! HMAC algorithm, and the PRK's mode), for an AEAD tag it agrees, and for a
//! cipher algorithm it also prints `block_len`, which rind computes. Those
//! strings are checked for what rind writes.

#![cfg_attr(not(feature = "wipe"), allow(unused_imports))]

#[cfg(not(feature = "wipe"))]
#[path = "../../rind/tests/freed/mod.rs"]
mod freed;

#[cfg(not(feature = "wipe"))]
#[global_allocator]
static ALLOCATOR: freed::Record = freed::Record;

use aws_lc_rs as theirs;
use rind_aws_lc_rs as ours;
use theirs::signature::KeyPair as _;

const RSA_PKCS8: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
const RSA_2047_PKCS1: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2047.pub.der");
const RSA_2049_PKCS8: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2049.pkcs8.der");

/// A 1024-bit RSA public key as PKCS#1. Its lengths use the one-byte long
/// form (`0x81`), which a 2048-bit key does not.
const RSA_1024_PKCS1: &[u8] = &[
    0x30, 0x81, 0x89, 0x02, 0x81, 0x81, 0x00, 0xb4, 0x19, 0x3a, 0x50, 0xf0, 0x42, 0x9d, 0x50, 0x00,
    0x22, 0x7f, 0x25, 0x44, 0xc0, 0x4e, 0x16, 0x71, 0x05, 0xe6, 0x89, 0x26, 0x45, 0x1e, 0x1c, 0x31,
    0x1e, 0xf8, 0x1e, 0x45, 0x84, 0x23, 0x32, 0xd7, 0x1b, 0x01, 0x8f, 0x27, 0xb9, 0xa8, 0x3a, 0x60,
    0x98, 0x7d, 0x33, 0xb3, 0x64, 0x3d, 0x04, 0xd2, 0x21, 0x16, 0xdb, 0x31, 0xdf, 0x96, 0x7b, 0x38,
    0x45, 0xa1, 0xd8, 0x8a, 0xef, 0x04, 0xa3, 0x1a, 0xc5, 0x0c, 0x75, 0xc8, 0x9e, 0xea, 0x89, 0x9c,
    0x6c, 0x92, 0xc5, 0x67, 0xcf, 0x69, 0xc6, 0xf7, 0xf2, 0x75, 0x2d, 0xb9, 0x60, 0xf2, 0xd7, 0x72,
    0x75, 0x77, 0x9c, 0x8c, 0xa1, 0x6d, 0x03, 0x4a, 0x18, 0x00, 0x97, 0xca, 0xf2, 0x53, 0xdb, 0x46,
    0x32, 0x7f, 0x16, 0x9f, 0x23, 0x3d, 0xe3, 0x80, 0x01, 0x78, 0xd8, 0x3b, 0xb1, 0xca, 0x8d, 0x22,
    0x01, 0x1b, 0x86, 0x4a, 0x15, 0xd7, 0xc9, 0x02, 0x03, 0x01, 0x00, 0x01,
];

fn same_debug(ours: &impl core::fmt::Debug, theirs: &impl core::fmt::Debug) {
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
}

fn shows(rendered: &str, needle: &str) {
    assert!(
        rendered.contains(needle),
        "{rendered:?} does not contain {needle:?}"
    );
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

/// `rsaEncryption` `SubjectPublicKeyInfo` around a PKCS#1 public key, with
/// the NULL parameters omitted, which both crates accept.
fn spki(pkcs1: &[u8]) -> Vec<u8> {
    const RSA_ENCRYPTION: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01];
    let bits = [&[0][..], pkcs1].concat();
    der(
        0x30,
        &[der(0x30, &der(0x06, RSA_ENCRYPTION)), der(0x03, &bits)].concat(),
    )
}

#[test]
fn fips_is_refused() {
    assert_eq!(
        ours::try_fips_mode().unwrap_err(),
        theirs::try_fips_mode().unwrap_err()
    );
    // aws-lc-rs can report CPU jitter entropy outside FIPS mode. rind never
    // does: it is not a FIPS module.
    assert_eq!(
        ours::try_fips_cpu_jitter_entropy().unwrap_err(),
        "FIPS CPU Jitter Entropy not enabled!"
    );
    // rind is not a FIPS module, whatever AWS-LC's header constant is.
    assert_eq!(ours::fips_version(), None);
    ours::init();
}

#[test]
#[allow(deprecated)]
fn errors_match_aws_lc() {
    use std::error::Error;

    let ours_err = ours::error::Unspecified;
    let theirs_err = theirs::error::Unspecified;
    assert_eq!(ours_err.to_string(), theirs_err.to_string());
    assert_eq!(ours_err.description(), theirs_err.description());
    assert!(ours_err.cause().is_none());
    assert!(theirs_err.cause().is_none());
    same_debug(&ours_err, &theirs_err);

    let cases = [
        ours::signature::Ed25519KeyPair::from_seed_unchecked(&[0; 31]).unwrap_err(),
        ours::signature::Ed25519KeyPair::from_seed_unchecked(&[0; 33]).unwrap_err(),
    ];
    let theirs_cases = [
        theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[0; 31]).unwrap_err(),
        theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[0; 33]).unwrap_err(),
    ];
    for ours_rejected in cases {
        // rind keeps its own reason in `Display`. `description_` stays the
        // name aws-lc-rs uses for a key it refused itself.
        assert_eq!(ours_rejected.to_string(), "an encoding of the wrong length");
        assert_eq!(ours_rejected.description_(), "InvalidEncoding");
        assert_eq!(ours_rejected.description(), ours_rejected.description_());
        assert!(Error::cause(&ours_rejected).is_none());
    }
    let _ = theirs_cases;
}

#[test]
fn constant_time_comparison_matches_aws_lc() {
    assert!(ours::constant_time::verify_slices_are_equal(b"same", b"same").is_ok());
    assert_eq!(
        ours::constant_time::verify_slices_are_equal(b"same", b"diff").is_ok(),
        theirs::constant_time::verify_slices_are_equal(b"same", b"diff").is_ok()
    );
    assert!(ours::constant_time::verify_slices_are_equal(b"same", b"same-more").is_err());
    assert!(ours::constant_time::verify_slices_are_equal(b"", b"x").is_err());
}

#[test]
#[allow(deprecated)]
fn digest_hmac_and_hkdf_surfaces_match_aws_lc() {
    let digests = [
        (
            &ours::digest::SHA1_FOR_LEGACY_USE_ONLY,
            &theirs::digest::SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (&ours::digest::SHA256, &theirs::digest::SHA256),
        (&ours::digest::SHA384, &theirs::digest::SHA384),
        (&ours::digest::SHA512, &theirs::digest::SHA512),
        (&ours::digest::SHA512_256, &theirs::digest::SHA512_256),
        (&ours::digest::SHA3_256, &theirs::digest::SHA3_256),
        (&ours::digest::SHA3_384, &theirs::digest::SHA3_384),
        (&ours::digest::SHA3_512, &theirs::digest::SHA3_512),
    ];
    for (ours_alg, theirs_alg) in digests {
        same_debug(ours_alg, theirs_alg);
        assert_eq!(ours_alg.output_len(), theirs_alg.output_len());
        assert_eq!(ours_alg.block_len(), theirs_alg.block_len());
        assert_eq!(ours_alg.chaining_len(), theirs_alg.chaining_len());
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(ours::digest::SHA256, ours::digest::SHA384);
    assert_ne!(ours::digest::SHA512, ours::digest::SHA512_256);
    let digest = ours::digest::digest(&ours::digest::SHA256, b"surfaces");
    let theirs_digest = theirs::digest::digest(&theirs::digest::SHA256, b"surfaces");
    same_debug(&digest, &theirs_digest);
    assert_eq!(
        format!("{:?}", digest.algorithm()),
        format!("{:?}", theirs_digest.algorithm())
    );

    let hmacs = [
        (
            ours::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
            theirs::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (ours::hmac::HMAC_SHA256, theirs::hmac::HMAC_SHA256),
        (ours::hmac::HMAC_SHA384, theirs::hmac::HMAC_SHA384),
        (ours::hmac::HMAC_SHA512, theirs::hmac::HMAC_SHA512),
    ];
    for (ours_alg, theirs_alg) in hmacs {
        same_debug(&ours_alg, &theirs_alg);
        assert_eq!(ours_alg.tag_len(), theirs_alg.tag_len());
        same_debug(ours_alg.digest_algorithm(), theirs_alg.digest_algorithm());
        assert_eq!(ours_alg, ours_alg);
        let ours_key = ours::hmac::Key::new(ours_alg, b"key");
        let theirs_key = theirs::hmac::Key::new(theirs_alg, b"key");
        same_debug(&ours_key, &theirs_key);
        same_debug(&ours_key.algorithm(), &theirs_key.algorithm());
        let ours_ctx = ours::hmac::Context::with_key(&ours_key);
        let theirs_ctx = theirs::hmac::Context::with_key(&theirs_key);
        same_debug(&ours_ctx, &theirs_ctx);
        let mut out = vec![0; ours_alg.tag_len()];
        let mut theirs_out = vec![0; theirs_alg.tag_len()];
        assert_eq!(
            ours::hmac::sign_to_buffer(&ours_key, b"msg", &mut out).unwrap(),
            theirs::hmac::sign_to_buffer(&theirs_key, b"msg", &mut theirs_out).unwrap()
        );
        assert!(ours::hmac::sign_to_buffer(&ours_key, b"msg", &mut [0; 4]).is_err());
        assert!(theirs::hmac::sign_to_buffer(&theirs_key, b"msg", &mut [0; 4]).is_err());
    }
    assert_ne!(ours::hmac::HMAC_SHA256, ours::hmac::HMAC_SHA512);

    let hkdfs = [
        (ours::hkdf::HKDF_SHA256, theirs::hkdf::HKDF_SHA256),
        (
            ours::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
            theirs::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
        ),
    ];
    for (ours_alg, theirs_alg) in hkdfs {
        same_debug(&ours_alg, &theirs_alg);
        same_debug(&ours_alg.hmac_algorithm(), &theirs_alg.hmac_algorithm());
        let ours_salt = ours::hkdf::Salt::none(ours_alg);
        shows(&format!("{ours_salt:?}"), "hkdf::Salt");
        shows(&format!("{ours_salt:?}"), "SHA");
        let ours_prk = ours::hkdf::Prk::new_less_safe(ours_alg, b"prk");
        shows(&format!("{ours_prk:?}"), "hkdf::Prk");
        let info: &[&[u8]] = &[b"info"];
        let ours_okm = ours_prk.expand(info, ours_alg).unwrap();
        shows(&format!("{ours_okm:?}"), "hkdf::Okm");
        assert!(
            ours_prk
                .expand(info, Len(0))
                .unwrap()
                .fill(&mut [0; 1])
                .is_err()
        );
        assert!(theirs_prk_fill_mismatch(theirs_alg));
    }
}

fn theirs_prk_fill_mismatch(algorithm: theirs::hkdf::Algorithm) -> bool {
    theirs::hkdf::Prk::new_less_safe(algorithm, b"prk")
        .expand(&[b"info"], Len(0))
        .unwrap()
        .fill(&mut [0; 1])
        .is_err()
}

struct Len(usize);

impl ours::hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

impl theirs::hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

#[test]
fn random_bytes_are_not_a_constant() {
    same_debug(
        &ours::rand::SystemRandom::new(),
        &theirs::rand::SystemRandom::new(),
    );
    let mut first = [0x5a; 32];
    let mut second = [0x5a; 32];
    ours::rand::fill(&mut first).unwrap();
    ours::rand::fill(&mut second).unwrap();
    assert_ne!(first, [0x5a; 32]);
    assert_ne!(first, [0; 32]);
    assert_ne!(first, [1; 32]);
    assert_ne!(first, second);
    let rng = ours::rand::SystemRandom::new();
    let generated = ours::rand::generate::<[u8; 16]>(&rng).unwrap().expose();
    assert_ne!(generated, [0; 16]);
    assert_ne!(generated, [1; 16]);
    let mut via_trait = [0x5a; 8];
    ours::rand::SecureRandom::fill(&rng, &mut via_trait).unwrap();
    assert_ne!(via_trait, [0x5a; 8]);
}

#[test]
fn iv_length_matches_aws_lc() {
    let iv = ours::iv::FixedLength::<16>::from([9u8; 16]);
    let theirs_iv = theirs::iv::FixedLength::<16>::from([9u8; 16]);
    assert_eq!(iv.size(), theirs_iv.size());
    assert_eq!(iv.as_ref(), &[9; 16]);
    assert_eq!(theirs_iv.as_ref(), &[9; 16]);
    let from_array: ours::iv::FixedLength<16> = [3u8; 16].into();
    assert_eq!(from_array.as_ref(), &[3; 16]);
    assert!(ours::iv::FixedLength::<16>::try_from([0u8; 15].as_slice()).is_err());
    let back: [u8; 16] = iv.try_into().unwrap();
    assert_eq!(back, [9; 16]);
    let drawn = [
        ours::iv::FixedLength::<16>::new().unwrap(),
        ours::iv::FixedLength::<16>::new().unwrap(),
    ];
    assert_ne!(drawn[0].as_ref(), drawn[1].as_ref());
    assert_ne!(drawn[0].as_ref(), &[0; 16]);
}

#[test]
fn aead_quic_and_tls_surfaces_match_aws_lc() {
    use ours::aead::BoundKey as _;
    use theirs::aead::BoundKey as _;

    let algorithms = [
        (&ours::aead::AES_128_GCM, &theirs::aead::AES_128_GCM, 16),
        (&ours::aead::AES_192_GCM, &theirs::aead::AES_192_GCM, 24),
        (&ours::aead::AES_256_GCM, &theirs::aead::AES_256_GCM, 32),
        (
            &ours::aead::CHACHA20_POLY1305,
            &theirs::aead::CHACHA20_POLY1305,
            32,
        ),
    ];
    for (ours_alg, theirs_alg, key_len) in algorithms {
        same_debug(ours_alg, theirs_alg);
        assert_eq!(ours_alg.key_len(), theirs_alg.key_len());
        assert_eq!(ours_alg.tag_len(), theirs_alg.tag_len());
        assert_eq!(ours_alg.nonce_len(), theirs_alg.nonce_len());
        assert_eq!(ours_alg.key_len(), key_len);
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(ours::aead::AES_128_GCM, ours::aead::AES_256_GCM);
    assert_ne!(ours::aead::AES_128_GCM, ours::aead::CHACHA20_POLY1305);
    assert_ne!(ours::aead::AES_192_GCM, ours::aead::AES_128_GCM);

    let nonce_bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    let ours_nonce = ours::aead::Nonce::assume_unique_for_key(nonce_bytes);
    let theirs_nonce = theirs::aead::Nonce::assume_unique_for_key(nonce_bytes);
    assert_eq!(ours_nonce.as_ref(), theirs_nonce.as_ref());
    assert_eq!(
        ours::aead::Nonce::try_assume_unique_for_key(&nonce_bytes)
            .unwrap()
            .as_ref(),
        &nonce_bytes
    );
    assert!(ours::aead::Nonce::try_assume_unique_for_key(&[0; 11]).is_err());
    let iv16 = [7u8; 16];
    assert_eq!(
        ours::aead::Nonce::from(&iv16).as_ref(),
        theirs::aead::Nonce::from(&iv16).as_ref()
    );
    let words = [0x0403_0201, 0x0807_0605, 0x0c0b_0a09];
    #[allow(deprecated)]
    {
        assert_eq!(
            ours::aead::Nonce::from(&words).as_ref(),
            theirs::aead::Nonce::from(&words).as_ref()
        );
    }

    let key = [0x11; 32];
    let aad = b"aad-surfaces";
    let msg = b"message-surfaces";
    let ours_key = ours::aead::LessSafeKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key[..16]).unwrap(),
    );
    let theirs_key = theirs::aead::LessSafeKey::new(
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key[..16]).unwrap(),
    );
    same_debug(ours_key.algorithm(), theirs_key.algorithm());
    same_debug(&ours_key, &theirs_key);
    let ours_unbound = ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key[..16]).unwrap();
    let theirs_unbound =
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key[..16]).unwrap();
    same_debug(&ours_unbound, &theirs_unbound);

    let mut ours_sealed = msg.to_vec();
    #[allow(deprecated)]
    ours_key
        .seal_in_place(
            ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
            ours::aead::Aad::from(aad),
            &mut ours_sealed,
        )
        .unwrap();
    let mut theirs_sealed = msg.to_vec();
    #[allow(deprecated)]
    theirs_key
        .seal_in_place(
            theirs::aead::Nonce::assume_unique_for_key(nonce_bytes),
            theirs::aead::Aad::from(aad),
            &mut theirs_sealed,
        )
        .unwrap();
    assert_eq!(ours_sealed, theirs_sealed);

    let mut plaintext = ours_sealed.clone();
    let opened = ours_key
        .open_within(
            ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
            ours::aead::Aad::from(aad),
            &mut plaintext,
            0..,
        )
        .unwrap();
    assert_eq!(opened, msg);

    let (ciphertext, tag) = ours_sealed.split_at(ours_sealed.len() - 16);
    let mut gathered = vec![0; ciphertext.len()];
    ours_key
        .open_separate_gather(
            ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
            ours::aead::Aad::from(aad),
            ciphertext,
            tag,
            &mut gathered,
        )
        .unwrap();
    assert_eq!(gathered, msg);
    assert!(
        ours_key
            .open_separate_gather(
                ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
                ours::aead::Aad::empty(),
                ciphertext,
                tag,
                &mut vec![0; ciphertext.len() + 1],
            )
            .is_err()
    );
    let mut theirs_gathered = vec![0; ciphertext.len()];
    theirs_key
        .open_separate_gather(
            theirs::aead::Nonce::assume_unique_for_key(nonce_bytes),
            theirs::aead::Aad::from(aad),
            ciphertext,
            tag,
            &mut theirs_gathered,
        )
        .unwrap();
    assert_eq!(gathered, theirs_gathered);

    let extra = b"extra";
    let mut out_ciphertext = vec![0; msg.len()];
    let mut extra_out = vec![0; extra.len() + 16];
    ours_key
        .seal_out_of_place_scatter(
            ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
            ours::aead::Aad::from(aad),
            msg,
            &mut out_ciphertext,
            extra,
            &mut extra_out,
        )
        .unwrap();
    let mut theirs_out = vec![0; msg.len()];
    let mut theirs_extra = vec![0; extra.len() + 16];
    theirs_key
        .seal_out_of_place_scatter(
            theirs::aead::Nonce::assume_unique_for_key(nonce_bytes),
            theirs::aead::Aad::from(aad),
            msg,
            &mut theirs_out,
            extra,
            &mut theirs_extra,
        )
        .unwrap();
    assert_eq!(out_ciphertext, theirs_out);
    assert_eq!(extra_out, theirs_extra);
    assert!(
        ours_key
            .seal_in_place_scatter(
                ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
                ours::aead::Aad::empty(),
                &mut out_ciphertext.clone(),
                extra,
                &mut vec![0; extra.len()],
            )
            .is_err()
    );
    let mut in_place = msg.to_vec();
    let mut tag_only = vec![0; 16];
    ours_key
        .seal_in_place_scatter(
            ours::aead::Nonce::assume_unique_for_key(nonce_bytes),
            ours::aead::Aad::from(aad),
            &mut in_place,
            &[],
            &mut tag_only,
        )
        .unwrap();
    assert_eq!(&in_place, &theirs_out[..msg.len()]);

    let mut ours_sealing = ours::aead::SealingKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key[..16]).unwrap(),
        ours::aead::nonce_sequence::Counter32Builder::new()
            .identifier([9; 8])
            .counter(4)
            .limit(3)
            .build(),
    );
    let mut theirs_sealing = theirs::aead::SealingKey::new(
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key[..16]).unwrap(),
        theirs::aead::nonce_sequence::Counter32Builder::new()
            .identifier([9; 8])
            .counter(4)
            .limit(3)
            .build(),
    );
    same_debug(&ours_sealing, &theirs_sealing);
    let prepared = ours_sealing.prepare_nonce().unwrap();
    let theirs_prepared = theirs_sealing.prepare_nonce().unwrap();
    same_debug(&prepared, &theirs_prepared);
    assert_eq!(prepared.nonce().as_ref(), theirs_prepared.nonce().as_ref());
    let mut sealed = msg.to_vec();
    let tag = prepared
        .seal_in_place_separate_tag(ours::aead::Aad::from(aad), &mut sealed)
        .unwrap();
    same_debug(&tag, &{
        let mut theirs_sealed = msg.to_vec();
        theirs_prepared
            .seal_in_place_separate_tag(theirs::aead::Aad::from(aad), &mut theirs_sealed)
            .unwrap()
    });
    assert_eq!(sealed.len(), msg.len());

    let mut ours_opening = ours::aead::OpeningKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key[..16]).unwrap(),
        ours::aead::nonce_sequence::Counter32Builder::new()
            .identifier([9; 8])
            .counter(4)
            .build(),
    );
    same_debug(
        &ours_opening,
        &theirs::aead::OpeningKey::new(
            theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key[..16]).unwrap(),
            theirs::aead::nonce_sequence::Counter32Builder::new()
                .identifier([9; 8])
                .counter(4)
                .build(),
        ),
    );
    let mut opening_buf = sealed.clone();
    opening_buf.extend_from_slice(tag.as_ref());
    let mut prefixed = vec![0xab; 4];
    prefixed.extend_from_slice(&opening_buf);
    let opened = ours_opening
        .open_within(ours::aead::Aad::from(aad), &mut prefixed, 4..)
        .unwrap();
    assert_eq!(opened, msg);
    let prepared = ours_opening.prepare_nonce().unwrap();
    // aws-lc-rs prints the same empty non-exhaustive struct.
    shows(&format!("{prepared:?}"), "OpeningKeyPreparedNonce");
    shows(&format!("{prepared:?}"), "..");

    assert!(ours::aead::RandomizedNonceKey::new(&ours::aead::CHACHA20_POLY1305, &key).is_err());
    assert!(ours::aead::RandomizedNonceKey::new(&ours::aead::AES_192_GCM, &key[..24]).is_err());
    assert!(theirs::aead::RandomizedNonceKey::new(&theirs::aead::CHACHA20_POLY1305, &key).is_err());
    let random = ours::aead::RandomizedNonceKey::new(&ours::aead::AES_128_GCM, &key[..16]).unwrap();
    let theirs_random =
        theirs::aead::RandomizedNonceKey::new(&theirs::aead::AES_128_GCM, &key[..16]).unwrap();
    same_debug(&random, &theirs_random);
    let mut body = msg.to_vec();
    let nonce = random
        .seal_in_place_append_tag(ours::aead::Aad::from(aad), &mut body)
        .unwrap();
    assert_ne!(nonce.as_ref(), &[0; 12]);
    assert_ne!(nonce.as_ref(), &[1; 12]);
    let opened = random
        .open_in_place(
            ours::aead::Nonce::assume_unique_for_key(*nonce.as_ref()),
            ours::aead::Aad::from(aad),
            &mut body,
        )
        .unwrap();
    assert_eq!(opened, msg);
    let mut once = msg.to_vec();
    let mut twice = msg.to_vec();
    let (n1, _) = random
        .seal_in_place_separate_tag(ours::aead::Aad::empty(), &mut once)
        .unwrap();
    let (n2, _) = random
        .seal_in_place_separate_tag(ours::aead::Aad::empty(), &mut twice)
        .unwrap();
    assert_ne!(n1.as_ref(), n2.as_ref());

    let quic = [
        (&ours::aead::quic::AES_128, &theirs::aead::quic::AES_128),
        (&ours::aead::quic::AES_256, &theirs::aead::quic::AES_256),
        (&ours::aead::quic::CHACHA20, &theirs::aead::quic::CHACHA20),
    ];
    for (ours_alg, theirs_alg) in quic {
        same_debug(ours_alg, theirs_alg);
        assert_eq!(ours_alg.key_len(), theirs_alg.key_len());
        assert_eq!(ours_alg.sample_len(), theirs_alg.sample_len());
        assert_eq!(ours_alg, ours_alg);
        let ours_hp =
            ours::aead::quic::HeaderProtectionKey::new(ours_alg, &key[..ours_alg.key_len()])
                .unwrap();
        let theirs_hp =
            theirs::aead::quic::HeaderProtectionKey::new(theirs_alg, &key[..theirs_alg.key_len()])
                .unwrap();
        let sample = [0x3c; 16];
        assert_eq!(
            ours_hp.new_mask(&sample).unwrap(),
            theirs_hp.new_mask(&sample).unwrap()
        );
        assert!(ours_hp.new_mask(&[0; 15]).is_err());
    }
    assert_ne!(ours::aead::quic::AES_128, ours::aead::quic::AES_256);
    assert_ne!(ours::aead::quic::AES_128, ours::aead::quic::CHACHA20);

    let mut ours_tls = ours::aead::TlsRecordSealingKey::new(
        &ours::aead::AES_128_GCM,
        ours::aead::TlsProtocolId::TLS13,
        &key[..16],
    )
    .unwrap();
    let mut theirs_tls = theirs::aead::TlsRecordSealingKey::new(
        &theirs::aead::AES_128_GCM,
        theirs::aead::TlsProtocolId::TLS13,
        &key[..16],
    )
    .unwrap();
    // aws-lc-rs names the inner key `UnboundKey`; rind names the wrapper `LessSafeKey`.
    shows(&format!("{ours_tls:?}"), "TlsRecordSealingKey");
    shows(&format!("{ours_tls:?}"), "AES_128_GCM");
    shows(&format!("{ours_tls:?}"), "TLS13");
    shows(&format!("{theirs_tls:?}"), "TlsRecordSealingKey");
    assert_eq!(
        format!("{:?}", ours_tls.tls_protocol_id()),
        format!("{:?}", theirs_tls.tls_protocol_id())
    );
    same_debug(ours_tls.algorithm(), theirs_tls.algorithm());
    let mut tls_nonce = [0; 12];
    tls_nonce[11] = 1;
    let mut ours_record = msg.to_vec();
    let ours_tag = ours_tls
        .seal_in_place_separate_tag(
            ours::aead::Nonce::assume_unique_for_key(tls_nonce),
            ours::aead::Aad::from(aad),
            &mut ours_record,
        )
        .unwrap();
    let mut theirs_record = msg.to_vec();
    let theirs_tag = theirs_tls
        .seal_in_place_separate_tag(
            theirs::aead::Nonce::assume_unique_for_key(tls_nonce),
            theirs::aead::Aad::from(aad),
            &mut theirs_record,
        )
        .unwrap();
    assert_eq!(ours_record, theirs_record);
    assert_eq!(ours_tag.as_ref(), theirs_tag.as_ref());
    same_debug(&ours_tag, &theirs_tag);
    let ours_open = ours::aead::TlsRecordOpeningKey::new(
        &ours::aead::AES_128_GCM,
        ours::aead::TlsProtocolId::TLS13,
        &key[..16],
    )
    .unwrap();
    let theirs_open = theirs::aead::TlsRecordOpeningKey::new(
        &theirs::aead::AES_128_GCM,
        theirs::aead::TlsProtocolId::TLS13,
        &key[..16],
    )
    .unwrap();
    shows(&format!("{ours_open:?}"), "TlsRecordOpeningKey");
    shows(&format!("{ours_open:?}"), "TLS13");
    shows(&format!("{theirs_open:?}"), "TlsRecordOpeningKey");
    let mut record = ours_record.clone();
    record.extend_from_slice(theirs_tag.as_ref());
    let mut prefixed = vec![1, 2, 3];
    prefixed.extend_from_slice(&record);
    assert_eq!(
        ours_open
            .open_within(
                ours::aead::Nonce::assume_unique_for_key(tls_nonce),
                ours::aead::Aad::from(aad),
                &mut prefixed,
                3..,
            )
            .unwrap(),
        msg
    );
    let mut direct = record.clone();
    assert_eq!(
        ours_open
            .open_in_place(
                ours::aead::Nonce::assume_unique_for_key(tls_nonce),
                ours::aead::Aad::from(aad),
                &mut direct,
            )
            .unwrap(),
        msg
    );
    let mut theirs_direct = record;
    assert_eq!(
        theirs_open
            .open_in_place(
                theirs::aead::Nonce::assume_unique_for_key(tls_nonce),
                theirs::aead::Aad::from(aad),
                &mut theirs_direct,
            )
            .unwrap(),
        msg
    );
    assert!(
        ours::aead::TlsRecordOpeningKey::new(
            &ours::aead::AES_192_GCM,
            ours::aead::TlsProtocolId::TLS12,
            &key[..24],
        )
        .is_err()
    );
    assert!(
        theirs::aead::TlsRecordSealingKey::new(
            &theirs::aead::CHACHA20_POLY1305,
            theirs::aead::TlsProtocolId::TLS12,
            &key,
        )
        .is_err()
    );
}

/// `SealingKey` and `OpeningKey` entry points the prepared-nonce calls do not reach.
#[test]
fn bound_aead_keys_match_aws_lc() {
    use ours::aead::BoundKey as _;
    use theirs::aead::BoundKey as _;

    let key = [0x21; 16];
    let aad = b"bound";
    let msg = b"bound-message";
    let sequence = |counter: u32| {
        (
            ours::aead::nonce_sequence::Counter32Builder::new()
                .identifier([3; 8])
                .counter(counter)
                .build(),
            theirs::aead::nonce_sequence::Counter32Builder::new()
                .identifier([3; 8])
                .counter(counter)
                .build(),
        )
    };
    let (ours_seq, theirs_seq) = sequence(1);
    let mut ours_sealing = ours::aead::SealingKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key).unwrap(),
        ours_seq,
    );
    let mut theirs_sealing = theirs::aead::SealingKey::new(
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key).unwrap(),
        theirs_seq,
    );
    let mut ours_buf = msg.to_vec();
    let mut theirs_buf = msg.to_vec();
    #[allow(deprecated)]
    {
        ours_sealing
            .seal_in_place(ours::aead::Aad::from(aad), &mut ours_buf)
            .unwrap();
        theirs_sealing
            .seal_in_place(theirs::aead::Aad::from(aad), &mut theirs_buf)
            .unwrap();
    }
    assert_eq!(ours_buf, theirs_buf);

    let (ours_seq, theirs_seq) = sequence(1);
    let mut ours_opening = ours::aead::OpeningKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key).unwrap(),
        ours_seq,
    );
    let mut theirs_opening = theirs::aead::OpeningKey::new(
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key).unwrap(),
        theirs_seq,
    );
    assert_eq!(
        ours_opening
            .open_in_place(ours::aead::Aad::from(aad), &mut ours_buf)
            .unwrap(),
        msg
    );
    assert_eq!(
        theirs_opening
            .open_in_place(theirs::aead::Aad::from(aad), &mut theirs_buf)
            .unwrap(),
        msg
    );

    let (ours_seq, theirs_seq) = sequence(9);
    let mut ours_sealing = ours::aead::SealingKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key).unwrap(),
        ours_seq,
    );
    let mut theirs_sealing = theirs::aead::SealingKey::new(
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key).unwrap(),
        theirs_seq,
    );
    let mut ours_body = msg.to_vec();
    let mut theirs_body = msg.to_vec();
    ours_sealing
        .seal_in_place_append_tag(ours::aead::Aad::from(aad), &mut ours_body)
        .unwrap();
    theirs_sealing
        .seal_in_place_append_tag(theirs::aead::Aad::from(aad), &mut theirs_body)
        .unwrap();
    assert_eq!(ours_body, theirs_body);

    let (ours_seq, theirs_seq) = sequence(11);
    let mut ours_sealing = ours::aead::SealingKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key).unwrap(),
        ours_seq,
    );
    let mut theirs_sealing = theirs::aead::SealingKey::new(
        theirs::aead::UnboundKey::new(&theirs::aead::AES_128_GCM, &key).unwrap(),
        theirs_seq,
    );
    let prepared = ours_sealing.prepare_nonce().unwrap();
    let theirs_prepared = theirs_sealing.prepare_nonce().unwrap();
    let mut ours_prepared = msg.to_vec();
    let mut theirs_prepared_buf = msg.to_vec();
    prepared
        .seal_in_place_append_tag(ours::aead::Aad::from(aad), &mut ours_prepared)
        .unwrap();
    theirs_prepared
        .seal_in_place_append_tag(theirs::aead::Aad::from(aad), &mut theirs_prepared_buf)
        .unwrap();
    assert_eq!(ours_prepared, theirs_prepared_buf);

    let (ours_seq, _) = sequence(11);
    let mut ours_opening = ours::aead::OpeningKey::new(
        ours::aead::UnboundKey::new(&ours::aead::AES_128_GCM, &key).unwrap(),
        ours_seq,
    );
    assert_eq!(
        ours_opening
            .prepare_nonce()
            .unwrap()
            .open_in_place(ours::aead::Aad::from(aad), &mut ours_prepared)
            .unwrap(),
        msg
    );
}

#[test]
fn cipher_surfaces_match_aws_lc() {
    let ciphers = [
        (&ours::cipher::AES_128, &theirs::cipher::AES_128),
        (&ours::cipher::AES_192, &theirs::cipher::AES_192),
        (&ours::cipher::AES_256, &theirs::cipher::AES_256),
    ];
    for (ours_alg, theirs_alg) in ciphers {
        assert_eq!(ours_alg.block_len(), theirs_alg.block_len());
        assert_eq!(ours_alg, ours_alg);
        shows(&format!("{ours_alg:?}"), "Aes");
    }
    assert_ne!(ours::cipher::AES_128, ours::cipher::AES_256);

    let key_bytes = [0x42; 16];
    let ours_unbound =
        ours::cipher::UnboundCipherKey::new(&ours::cipher::AES_128, &key_bytes).unwrap();
    let theirs_unbound =
        theirs::cipher::UnboundCipherKey::new(&theirs::cipher::AES_128, &key_bytes).unwrap();
    shows(&format!("{ours_unbound:?}"), "UnboundCipherKey");
    shows(&format!("{theirs_unbound:?}"), "UnboundCipherKey");
    let ours_enc = ours::cipher::EncryptingKey::ctr(ours_unbound).unwrap();
    let theirs_enc = theirs::cipher::EncryptingKey::ctr(theirs_unbound).unwrap();
    shows(&format!("{ours_enc:?}"), "EncryptingKey");
    shows(&format!("{ours_enc:?}"), "CTR");
    assert_eq!(
        format!("{:?}", ours_enc.mode()),
        format!("{:?}", theirs_enc.mode())
    );
    let iv = [8u8; 16];
    let mut block = [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let mut theirs_block = block;
    let context = ours::cipher::EncryptionContext::Iv128(iv.into());
    shows(&format!("{context:?}"), "Iv128");
    let none = ours::cipher::EncryptionContext::None;
    shows(&format!("{none:?}"), "None");
    let mut rejected = block;
    assert!(ours_enc.less_safe_encrypt(&mut rejected, none).is_err());
    ours_enc.less_safe_encrypt(&mut block, context).unwrap();
    theirs_enc
        .less_safe_encrypt(
            &mut theirs_block,
            theirs::cipher::EncryptionContext::Iv128(iv.into()),
        )
        .unwrap();
    assert_eq!(block, theirs_block);
    let decryption =
        ours::cipher::DecryptionContext::from(ours::cipher::EncryptionContext::Iv128(iv.into()));
    shows(&format!("{decryption:?}"), "Iv128");
    let ours_dec = ours::cipher::DecryptingKey::ctr(
        ours::cipher::UnboundCipherKey::new(&ours::cipher::AES_128, &key_bytes).unwrap(),
    )
    .unwrap();
    shows(&format!("{ours_dec:?}"), "DecryptingKey");
    let mut round = block;
    ours_dec.decrypt(&mut round, decryption).unwrap();
    assert_eq!(
        round,
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    );

    let padded = ours::cipher::PaddedBlockEncryptingKey::cbc_pkcs7(
        ours::cipher::UnboundCipherKey::new(&ours::cipher::AES_128, &key_bytes).unwrap(),
    )
    .unwrap();
    let theirs_padded = theirs::cipher::PaddedBlockEncryptingKey::cbc_pkcs7(
        theirs::cipher::UnboundCipherKey::new(&theirs::cipher::AES_128, &key_bytes).unwrap(),
    )
    .unwrap();
    shows(&format!("{padded:?}"), "PaddedBlockEncryptingKey");
    shows(&format!("{theirs_padded:?}"), "PaddedBlockEncryptingKey");
    shows(&format!("{:?}", padded.mode()), "CBC");
    let decrypting = ours::cipher::PaddedBlockDecryptingKey::cbc_pkcs7(
        ours::cipher::UnboundCipherKey::new(&ours::cipher::AES_128, &key_bytes).unwrap(),
    )
    .unwrap();
    shows(&format!("{decrypting:?}"), "PaddedBlockDecryptingKey");
    shows(
        &format!(
            "{:?}",
            theirs::cipher::PaddedBlockDecryptingKey::cbc_pkcs7(
                theirs::cipher::UnboundCipherKey::new(&theirs::cipher::AES_128, &key_bytes)
                    .unwrap(),
            )
            .unwrap()
        ),
        "PaddedBlockDecryptingKey",
    );
}

#[test]
fn agreement_surfaces_match_aws_lc() {
    use ours::encoding::{AsBigEndian as _, AsDer as _};
    use theirs::encoding::{AsBigEndian as _, AsDer as _};

    let algorithms = [
        (&ours::agreement::X25519, &theirs::agreement::X25519, 32),
        (
            &ours::agreement::ECDH_P256,
            &theirs::agreement::ECDH_P256,
            32,
        ),
        (
            &ours::agreement::ECDH_P384,
            &theirs::agreement::ECDH_P384,
            48,
        ),
        (
            &ours::agreement::ECDH_P521,
            &theirs::agreement::ECDH_P521,
            66,
        ),
    ];
    for (ours_alg, theirs_alg, len) in algorithms {
        same_debug(ours_alg, theirs_alg);
        assert_eq!(ours_alg, ours_alg);
        // One, which is inside every curve order. A repeated `0x11` is not,
        // once the scalar is 521 bits.
        let mut seed = vec![0u8; len];
        seed[len - 1] = 1;
        let ours_key = ours::agreement::PrivateKey::from_private_key(ours_alg, &seed).unwrap();
        let theirs_key =
            theirs::agreement::PrivateKey::from_private_key(theirs_alg, &seed).unwrap();
        same_debug(&ours_key, &theirs_key);
        let ours_public = ours_key.compute_public_key().unwrap();
        let theirs_public = theirs_key.compute_public_key().unwrap();
        assert_eq!(ours_public.as_ref(), theirs_public.as_ref());
        same_debug(&ours_public, &theirs_public);
        same_debug(ours_public.algorithm(), theirs_public.algorithm());
        let peer = ours_public.as_ref().to_vec();
        let ours_unparsed = ours::agreement::UnparsedPublicKey::new(ours_alg, peer.clone());
        let theirs_unparsed = theirs::agreement::UnparsedPublicKey::new(theirs_alg, peer.clone());
        same_debug(&ours_unparsed, &theirs_unparsed);
        assert_eq!(ours_unparsed.bytes(), &peer);
        let ours_parsed = ours::agreement::ParsedPublicKey::try_from(&ours_unparsed).unwrap();
        let theirs_parsed = theirs::agreement::ParsedPublicKey::try_from(theirs_unparsed).unwrap();
        assert_eq!(ours_parsed.as_ref(), peer.as_slice());
        assert_eq!(theirs_parsed.as_ref(), peer.as_slice());
        same_debug(&ours_parsed.format(), &theirs_parsed.format());
        same_debug(ours_parsed.alg(), theirs_parsed.alg());
        let secret = ours::agreement::agree(
            &ours_key,
            ours::agreement::UnparsedPublicKey::new(ours_alg, peer.clone()),
            (),
            |bytes| Ok::<_, ()>(bytes.to_vec()),
        )
        .unwrap();
        let ephemeral = ours::agreement::EphemeralPrivateKey::generate(
            ours_alg,
            &ours::rand::SystemRandom::new(),
        )
        .unwrap();
        shows(&format!("{ephemeral:?}"), "EphemeralPrivateKey");
        shows(&format!("{ephemeral:?}"), &format!("{:?}", ours_alg));
        let _ = secret;
    }
    assert_ne!(ours::agreement::X25519, ours::agreement::ECDH_P256);

    let seed = [0x22; 32];
    let ours_key =
        ours::agreement::PrivateKey::from_private_key(&ours::agreement::X25519, &seed).unwrap();
    let exported: ours::encoding::Curve25519SeedBin = ours_key.as_be_bytes().unwrap();
    let theirs_key =
        theirs::agreement::PrivateKey::from_private_key(&theirs::agreement::X25519, &seed).unwrap();
    let theirs_exported: theirs::encoding::Curve25519SeedBin = theirs_key.as_be_bytes().unwrap();
    assert_eq!(exported.as_ref(), theirs_exported.as_ref());
    shows(&format!("{:?}", *exported), "Buffer(...)");
    shows(&format!("{exported:?}"), "Curve25519SeedBin");
    assert!(
        ours::encoding::AsBigEndian::<ours::encoding::Curve25519SeedBin>::as_be_bytes(
            &ours::agreement::PrivateKey::from_private_key(
                &ours::agreement::ECDH_P256,
                &[0x33; 32]
            )
            .unwrap(),
        )
        .is_err()
    );
    assert!(
        ours::encoding::AsBigEndian::<ours::encoding::EcPrivateKeyBin>::as_be_bytes(&ours_key)
            .is_err()
    );

    let p256 = ours::agreement::PrivateKey::generate(&ours::agreement::ECDH_P256).unwrap();
    let scalar: ours::encoding::EcPrivateKeyBin = p256.as_be_bytes().unwrap();
    let loaded = theirs::agreement::PrivateKey::from_private_key(
        &theirs::agreement::ECDH_P256,
        scalar.as_ref(),
    )
    .unwrap();
    assert_eq!(
        p256.compute_public_key().unwrap().as_ref(),
        loaded.compute_public_key().unwrap().as_ref()
    );
    let compressed: ours::encoding::EcPublicKeyCompressedBin =
        p256.compute_public_key().unwrap().as_be_bytes().unwrap();
    let theirs_compressed: theirs::encoding::EcPublicKeyCompressedBin =
        loaded.compute_public_key().unwrap().as_be_bytes().unwrap();
    assert_eq!(compressed.as_ref(), theirs_compressed.as_ref());
    let uncompressed: ours::encoding::EcPublicKeyUncompressedBin =
        p256.compute_public_key().unwrap().as_be_bytes().unwrap();
    assert_eq!(
        uncompressed.as_ref(),
        p256.compute_public_key().unwrap().as_ref()
    );

    let rng = ours::rand::SystemRandom::new();
    let ephemeral =
        ours::agreement::EphemeralPrivateKey::generate(&ours::agreement::X25519, &rng).unwrap();
    let public = ephemeral.compute_public_key().unwrap();
    let again =
        ours::agreement::EphemeralPrivateKey::generate(&ours::agreement::X25519, &rng).unwrap();
    let secret = ours::agreement::agree_ephemeral(
        again,
        ours::agreement::UnparsedPublicKey::new(&ours::agreement::X25519, public.as_ref()),
        (),
        |secret| Ok::<_, ()>(secret.to_vec()),
    )
    .unwrap();
    assert_eq!(secret.len(), 32);
    assert!(secret.iter().any(|byte| *byte != 0));
}

#[test]
fn key_wrap_and_kem_surfaces_match_aws_lc() {
    same_debug(&ours::key_wrap::AES_128, &theirs::key_wrap::AES_128);
    same_debug(&ours::key_wrap::AES_256, &theirs::key_wrap::AES_256);
    assert_eq!(
        ours::key_wrap::BlockCipher::key_len(&ours::key_wrap::AES_128),
        theirs::key_wrap::BlockCipher::key_len(&theirs::key_wrap::AES_128)
    );
    assert_eq!(
        ours::key_wrap::BlockCipher::id(&ours::key_wrap::AES_256),
        ours::key_wrap::BlockCipherId::Aes256
    );
    let kek = ours::key_wrap::AesKek::new(&ours::key_wrap::AES_128, &[0x44; 16]).unwrap();
    let theirs_kek =
        theirs::key_wrap::AesKek::new(&theirs::key_wrap::AES_128, &[0x44; 16]).unwrap();
    same_debug(&kek, &theirs_kek);
    assert_eq!(
        format!("{:?}", kek.block_cipher_id()),
        format!("{:?}", theirs_kek.block_cipher_id())
    );

    same_debug(&ours::kem::ML_KEM_768, &theirs::kem::ML_KEM_768);
    assert_eq!(ours::kem::ML_KEM_768.id(), ours::kem::AlgorithmId::MlKem768);
    let key = ours::kem::DecapsulationKey::generate(&ours::kem::ML_KEM_768).unwrap();
    shows(&format!("{key:?}"), "DecapsulationKey");
    shows(&format!("{key:?}"), "MlKem768");
    let public = key.encapsulation_key().unwrap();
    shows(&format!("{public:?}"), "EncapsulationKey");
    assert!(ours::kem::EncapsulationKey::new(&ours::kem::ML_KEM_768, &[0; 8]).is_err());
    assert!(ours::kem::EncapsulationKey::new(&ours::kem::ML_KEM_768, &[0; 2000]).is_err());
    let bytes = public.key_bytes().unwrap();
    shows(&format!("{bytes:?}"), "EncapsulationKeyBytes");
    assert_eq!(
        ours::kem::EncapsulationKey::new(&ours::kem::ML_KEM_768, bytes.as_ref())
            .unwrap()
            .key_bytes()
            .unwrap()
            .as_ref(),
        bytes.as_ref()
    );
}

#[test]
fn rsa_surfaces_match_aws_lc() {
    use ours::encoding::AsDer as _;
    use ours::signature::KeyPair as _;
    use theirs::encoding::AsDer as _;

    for (ours_size, theirs_size, len) in [
        (
            ours::rsa::KeySize::Rsa2048,
            theirs::rsa::KeySize::Rsa2048,
            256,
        ),
        (
            ours::rsa::KeySize::Rsa3072,
            theirs::rsa::KeySize::Rsa3072,
            384,
        ),
        (
            ours::rsa::KeySize::Rsa4096,
            theirs::rsa::KeySize::Rsa4096,
            512,
        ),
        (
            ours::rsa::KeySize::Rsa8192,
            theirs::rsa::KeySize::Rsa8192,
            1024,
        ),
    ] {
        same_debug(&ours_size, &theirs_size);
        assert_eq!(ours_size.len(), theirs_size.len());
        assert_eq!(ours_size.len(), len);
    }

    let ours_pair = ours::rsa::KeyPair::from_pkcs8(RSA_PKCS8).unwrap();
    let theirs_pair = theirs::rsa::KeyPair::from_pkcs8(RSA_PKCS8).unwrap();
    same_debug(&ours_pair, &theirs_pair);
    same_debug(ours_pair.public_key(), theirs_pair.public_key());
    assert_eq!(
        ours_pair.public_key().modulus_len(),
        theirs_pair.public_key().modulus_len()
    );
    assert_eq!(
        ours_pair.public_key().modulus().first_byte(),
        theirs_pair.public_key().modulus().first_byte()
    );
    assert_eq!(
        ours_pair.public_key().exponent().first_byte(),
        theirs_pair.public_key().exponent().first_byte()
    );
    assert_eq!(
        ours_pair
            .public_key()
            .exponent()
            .big_endian_without_leading_zero(),
        theirs_pair
            .public_key()
            .exponent()
            .big_endian_without_leading_zero()
    );

    let pkcs1 = ours_pair.public_key().as_ref();
    assert_eq!(
        ours::rsa::RsaParameters::public_modulus_len(pkcs1).unwrap(),
        theirs::rsa::RsaParameters::public_modulus_len(pkcs1).unwrap()
    );
    assert_eq!(
        ours::rsa::RsaParameters::public_modulus_len(RSA_2047_PKCS1).unwrap(),
        theirs::rsa::RsaParameters::public_modulus_len(RSA_2047_PKCS1).unwrap()
    );
    assert_eq!(
        ours::rsa::PublicKey::from_der(RSA_1024_PKCS1)
            .unwrap()
            .modulus_len(),
        theirs::rsa::PublicKey::from_der(RSA_1024_PKCS1)
            .unwrap()
            .modulus_len()
    );
    assert_eq!(
        ours::rsa::RsaParameters::public_modulus_len(RSA_1024_PKCS1).unwrap(),
        theirs::rsa::RsaParameters::public_modulus_len(RSA_1024_PKCS1).unwrap()
    );

    let small = spki(RSA_1024_PKCS1);
    let ours_small = ours::rsa::PublicEncryptingKey::from_der(&small).unwrap_err();
    let pkcs1_as_spki = ours::rsa::PublicEncryptingKey::from_der(pkcs1).unwrap_err();
    // A real but too-small SPKI is refused by rind, which keeps its reason.
    assert_eq!(ours_small.description_(), "InvalidEncoding");
    assert_eq!(
        ours_small.to_string(),
        "an RSA modulus that is negative, even, or of unsupported size"
    );
    // PKCS#1 is not an SPKI. `is_spki` replaced with `true` lets it through
    // to rind, whose reason is the sentence above rather than this name.
    assert_eq!(pkcs1_as_spki.description_(), "InvalidEncoding");
    assert_eq!(pkcs1_as_spki.to_string(), "InvalidEncoding");

    let wide = ours::rsa::PrivateDecryptingKey::from_pkcs8(RSA_2049_PKCS8).unwrap();
    let theirs_wide = theirs::rsa::PrivateDecryptingKey::from_pkcs8(RSA_2049_PKCS8).unwrap();
    assert_eq!(wide.key_size_bits(), theirs_wide.key_size_bits());
    assert_eq!(wide.key_size_bytes(), theirs_wide.key_size_bytes());
    assert_eq!(
        wide.public_key().key_size_bits(),
        theirs_wide.public_key().key_size_bits()
    );
    same_debug(&wide, &theirs_wide);
    same_debug(&wide.public_key(), &theirs_wide.public_key());
    let ours_oaep = ours::rsa::OaepPrivateDecryptingKey::new(wide).unwrap();
    let theirs_oaep = theirs::rsa::OaepPrivateDecryptingKey::new(theirs_wide).unwrap();
    same_debug(&ours_oaep, &theirs_oaep);
    assert_eq!(ours_oaep.key_size_bits(), theirs_oaep.key_size_bits());
    assert_eq!(ours_oaep.min_output_size(), theirs_oaep.min_output_size());
    let spki_bytes = spki(pkcs1);
    let encrypting = ours::rsa::OaepPublicEncryptingKey::new(
        ours::rsa::PublicEncryptingKey::from_der(&spki_bytes).unwrap(),
    )
    .unwrap();
    let theirs_encrypting = theirs::rsa::OaepPublicEncryptingKey::new(
        theirs::rsa::PublicEncryptingKey::from_der(&spki_bytes).unwrap(),
    )
    .unwrap();
    same_debug(&encrypting, &theirs_encrypting);
    assert_eq!(
        encrypting.key_size_bits(),
        theirs_encrypting.key_size_bits()
    );
    assert_eq!(
        encrypting.key_size_bytes(),
        theirs_encrypting.key_size_bytes()
    );
    for (ours_alg, theirs_alg) in [
        (
            &ours::rsa::OAEP_SHA1_MGF1SHA1,
            &theirs::rsa::OAEP_SHA1_MGF1SHA1,
        ),
        (
            &ours::rsa::OAEP_SHA256_MGF1SHA256,
            &theirs::rsa::OAEP_SHA256_MGF1SHA256,
        ),
        (
            &ours::rsa::OAEP_SHA384_MGF1SHA384,
            &theirs::rsa::OAEP_SHA384_MGF1SHA384,
        ),
        (
            &ours::rsa::OAEP_SHA512_MGF1SHA512,
            &theirs::rsa::OAEP_SHA512_MGF1SHA512,
        ),
    ] {
        same_debug(ours_alg, theirs_alg);
        same_debug(&ours_alg.id(), &theirs_alg.id());
        assert_eq!(
            encrypting.max_plaintext_size(ours_alg),
            theirs_encrypting.max_plaintext_size(theirs_alg)
        );
    }

    const WITH_MAX: ours::signature::RsaParameters = ours::signature::RSA_PSS_2048_8192_SHA256
        .with_pss_salt_length(ours::signature::RsaPssSaltLength::Max);
    const THEIRS_MAX: theirs::signature::RsaParameters =
        theirs::signature::RSA_PSS_2048_8192_SHA256
            .with_pss_salt_length(theirs::signature::RsaPssSaltLength::Max);
    assert_eq!(
        ours::signature::RSA_PSS_2048_8192_SHA256,
        ours::signature::RSA_PSS_2048_8192_SHA256
    );
    assert_ne!(ours::signature::RSA_PSS_2048_8192_SHA256, WITH_MAX);
    assert_ne!(
        ours::signature::RSA_PKCS1_2048_8192_SHA256,
        ours::signature::RSA_PKCS1_2048_8192_SHA384
    );
    assert_ne!(
        WITH_MAX,
        ours::signature::RSA_PSS_2048_8192_SHA384
            .with_pss_salt_length(ours::signature::RsaPssSaltLength::Max)
    );
    same_debug(
        &ours::signature::RSA_PKCS1_2048_8192_SHA256,
        &theirs::signature::RSA_PKCS1_2048_8192_SHA256,
    );
    same_debug(&WITH_MAX, &THEIRS_MAX);
    same_debug(
        &ours::signature::RSA_PSS_SHA256,
        &theirs::signature::RSA_PSS_SHA256,
    );
    const SIGN_MAX: ours::signature::RsaSignatureEncoding = ours::signature::RSA_PSS_SHA256
        .with_pss_salt_length(ours::signature::RsaPssSaltLength::Custom(20));
    const THEIRS_SIGN_MAX: theirs::signature::RsaSignatureEncoding =
        theirs::signature::RSA_PSS_SHA256
            .with_pss_salt_length(theirs::signature::RsaPssSaltLength::Custom(20));
    same_debug(&SIGN_MAX, &THEIRS_SIGN_MAX);
    same_debug(
        &ours::signature::RSA_PKCS1_SHA256,
        &theirs::signature::RSA_PKCS1_SHA256,
    );
    assert_eq!(
        ours::signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY.min_modulus_len(),
        theirs::signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY.min_modulus_len()
    );
    assert_eq!(
        ours::signature::RSA_PKCS1_3072_8192_SHA384.max_modulus_len(),
        theirs::signature::RSA_PKCS1_3072_8192_SHA384.max_modulus_len()
    );

    let components = ours::rsa::PublicKeyComponents::<Vec<u8>>::from(ours_pair.public_key());
    let theirs_components =
        theirs::rsa::PublicKeyComponents::<Vec<u8>>::from(theirs_pair.public_key());
    same_debug(&components, &theirs_components);
    assert!(
        ours::rsa::PublicKeyComponents {
            n: vec![0, 1],
            e: vec![1, 0, 1],
        }
        .verify(
            &ours::signature::RSA_PKCS1_2048_8192_SHA256,
            b"msg",
            &[0; 256]
        )
        .is_err()
    );
    let mut signature = vec![0; ours_pair.public_modulus_len()];
    ours_pair
        .sign(
            &ours::signature::RSA_PKCS1_SHA256,
            &ours::rand::SystemRandom::new(),
            b"msg",
            &mut signature,
        )
        .unwrap();
    assert!(
        ours_pair
            .sign(
                &ours::signature::RSA_PKCS1_SHA256,
                &ours::rand::SystemRandom::new(),
                b"msg",
                &mut [0; 8],
            )
            .is_err()
    );
    let private = ours::rsa::OaepPrivateDecryptingKey::new(
        ours::rsa::PrivateDecryptingKey::from_pkcs8(RSA_PKCS8).unwrap(),
    )
    .unwrap();
    let mut ciphertext = vec![0; encrypting.ciphertext_size()];
    let ciphertext = encrypting
        .encrypt(
            &ours::rsa::OAEP_SHA256_MGF1SHA256,
            b"hi",
            &mut ciphertext,
            None,
        )
        .unwrap();
    // Longer than the minimum, which `<` replaced with `>` would refuse.
    let mut plaintext = vec![0; private.min_output_size() + 16];
    assert_eq!(
        private
            .decrypt(
                &ours::rsa::OAEP_SHA256_MGF1SHA256,
                ciphertext,
                &mut plaintext,
                None,
            )
            .unwrap(),
        b"hi"
    );

    let verifying = ours::signature::UnparsedPublicKey::new(
        &ours::signature::RSA_PKCS1_2048_8192_SHA256,
        pkcs1,
    );
    assert!(
        verifying
            .verify_digest(
                &ours::digest::digest(&ours::digest::SHA256, b"msg"),
                &signature
            )
            .is_err()
    );
    assert!(
        theirs::signature::UnparsedPublicKey::new(
            &theirs::signature::RSA_PKCS1_2048_8192_SHA256,
            pkcs1,
        )
        .verify(b"other", &signature)
        .is_err()
    );
}

#[test]
fn signature_surfaces_match_aws_lc() {
    use ours::encoding::{AsBigEndian as _, AsDer as _};
    use ours::signature::KeyPair as _;
    use theirs::encoding::{AsBigEndian as _, AsDer as _};

    assert_eq!(
        ours::signature::ECDSA_P256_SHA256_ASN1,
        ours::signature::ECDSA_P256_SHA256_ASN1
    );
    assert_ne!(
        ours::signature::ECDSA_P256_SHA256_ASN1,
        ours::signature::ECDSA_P256_SHA256_FIXED
    );
    assert_ne!(
        ours::signature::ECDSA_P256_SHA256_ASN1,
        ours::signature::ECDSA_P384_SHA384_ASN1
    );
    assert_eq!(ours::signature::ED25519, ours::signature::ED25519);

    let seed = [0x55; 32];
    let ours_ed = ours::signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
    let theirs_ed = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
    same_debug(&ours_ed, &theirs_ed);
    same_debug(ours_ed.public_key(), theirs_ed.public_key());
    let ours_seed = ours_ed.seed().unwrap();
    same_debug(&ours_seed, &theirs_ed.seed().unwrap());
    assert_eq!(
        ours::encoding::AsBigEndian::<ours::encoding::Curve25519SeedBin>::as_be_bytes(&ours_seed)
            .unwrap()
            .as_ref(),
        &seed
    );
    assert_eq!(
        ours_ed.try_sign(b"msg").unwrap().as_ref(),
        ours_ed.sign(b"msg").as_ref()
    );
    let signature = ours_ed.sign(b"msg");
    let key = ours::signature::UnparsedPublicKey::new(
        &ours::signature::ED25519,
        ours_ed.public_key().as_ref(),
    );
    assert_eq!(key.as_ref(), ours_ed.public_key().as_ref());
    shows(&format!("{key:?}"), "UnparsedPublicKey");
    assert!(
        key.verify_digest(
            &ours::digest::digest(&ours::digest::SHA256, b"msg"),
            signature.as_ref()
        )
        .is_err()
    );
    assert!(
        theirs::signature::UnparsedPublicKey::new(
            &theirs::signature::ED25519,
            theirs_ed.public_key().as_ref()
        )
        .verify_digest(
            &theirs::digest::digest(&theirs::digest::SHA256, b"msg"),
            signature.as_ref(),
        )
        .is_err()
    );
    let pkcs8 = ours_ed.to_pkcs8().unwrap();
    assert_eq!(pkcs8.as_ref(), theirs_ed.to_pkcs8().unwrap().as_ref());
    shows(
        &format!("{:?}", ours_ed.public_key().as_der().unwrap()),
        "PublicKeyX509Der",
    );

    let rng = ours::rand::SystemRandom::new();
    let pkcs8 = ours::signature::EcdsaKeyPair::generate_pkcs8(
        &ours::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        &rng,
    )
    .unwrap();
    let ours_pair = ours::signature::EcdsaKeyPair::from_pkcs8(
        &ours::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        pkcs8.as_ref(),
    )
    .unwrap();
    let theirs_pair = theirs::signature::EcdsaKeyPair::from_pkcs8(
        &theirs::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        pkcs8.as_ref(),
    )
    .unwrap();
    same_debug(&ours_pair, &theirs_pair);
    same_debug(ours_pair.public_key(), theirs_pair.public_key());
    same_debug(&ours_pair.private_key(), &theirs_pair.private_key());
    assert_eq!(
        ours::encoding::AsBigEndian::<ours::encoding::EcPrivateKeyBin>::as_be_bytes(
            &ours_pair.private_key()
        )
        .unwrap()
        .as_ref(),
        theirs::encoding::AsBigEndian::<theirs::encoding::EcPrivateKeyBin>::as_be_bytes(
            &theirs_pair.private_key()
        )
        .unwrap()
        .as_ref()
    );
    let digest = ours::digest::digest(&ours::digest::SHA256, b"signed");
    let signature = ours_pair.sign_digest(&digest).unwrap();
    let verifying = ours::signature::UnparsedPublicKey::new(
        &ours::signature::ECDSA_P256_SHA256_ASN1,
        ours_pair.public_key().as_ref(),
    );
    assert!(verifying.verify_digest(&digest, signature.as_ref()).is_ok());
    let wrong = ours::digest::digest(&ours::digest::SHA384, b"signed");
    assert!(verifying.verify_digest(&wrong, signature.as_ref()).is_err());
    let tampered = {
        let mut bytes = signature.as_ref().to_vec();
        bytes[0] ^= 1;
        bytes
    };
    assert!(verifying.verify_digest(&digest, &tampered).is_err());
    let parsed = verifying.parse().unwrap();
    shows(&format!("{parsed:?}"), "ParsedPublicKey");
    assert_eq!(parsed.as_ref(), ours_pair.public_key().as_ref());
    assert!(parsed.verify_sig(b"signed", signature.as_ref()).is_ok());
    assert!(parsed.verify_sig(b"other", signature.as_ref()).is_err());
    assert!(parsed.verify_digest_sig(&digest, &tampered).is_err());
    assert!(ours_pair.sign_digest(&wrong).is_err());
    shows(
        &format!("{:?}", ours_pair.public_key().as_der().unwrap()),
        "PublicKeyX509Der",
    );
    let _ = theirs_pair;
}

/// Without the `wipe` feature a secret encoding's bytes are still in the
/// block it frees. Replacing `&&` with `||` in `Buffer::drop` zeroises them.
#[cfg(not(feature = "wipe"))]
#[test]
fn secret_encoding_is_not_wiped_without_the_feature() {
    use ours::agreement::PrivateKey;
    use ours::encoding::{AsBigEndian, Curve25519SeedBin};

    let key = PrivateKey::from_private_key(&ours::agreement::X25519, &[0x7e; 32]).unwrap();
    let seed = AsBigEndian::<Curve25519SeedBin>::as_be_bytes(&key).unwrap();
    let bytes = seed.as_ref().to_vec();
    assert!(bytes.iter().any(|byte| *byte != 0));
    let ((), blocks) = freed::freed(|| drop(seed));
    assert!(
        blocks
            .iter()
            .any(|block| block.windows(bytes.len()).any(|window| window == bytes)),
        "secret encoding was wiped while the wipe feature is off"
    );
}
