//! Small surfaces of rind-aws-lc-rs that no other test reaches, each checked
//! against aws-lc-rs: constants, comparisons, and refusals.

#![cfg(not(any(miri, target_family = "wasm")))]

use aws_lc_rs as theirs;
use rind_aws_lc_rs as ours;

/// rind has no FIPS CPU jitter entropy, so it says so. aws-lc-rs's non-FIPS
/// build reports AWS-LC's own jitter source, which rind does not have.
#[test]
fn fips_jitter_refused() {
    assert!(ours::try_fips_cpu_jitter_entropy().is_err());
}

/// An AEAD or QUIC algorithm equals itself and no other.
#[test]
fn algorithms_compare() {
    use ours::aead::{self, quic};
    let aeads = [
        &aead::AES_128_GCM,
        &aead::AES_256_GCM,
        &aead::CHACHA20_POLY1305,
    ];
    for (i, a) in aeads.iter().enumerate() {
        for (j, b) in aeads.iter().enumerate() {
            assert_eq!(a == b, i == j);
        }
    }
    let quics = [&quic::AES_128, &quic::AES_256, &quic::CHACHA20];
    for (i, a) in quics.iter().enumerate() {
        for (j, b) in quics.iter().enumerate() {
            assert_eq!(a == b, i == j);
        }
    }
}

/// QUIC header protection samples as many bytes as aws-lc-rs's.
#[test]
fn quic_sample_len() {
    use ours::aead::quic as o;
    use theirs::aead::quic as t;
    for (ours, theirs) in [
        (&o::AES_128, &t::AES_128),
        (&o::AES_256, &t::AES_256),
        (&o::CHACHA20, &t::CHACHA20),
    ] {
        assert_eq!(ours.sample_len(), theirs.sample_len());
    }
}

/// Each digest's chaining length is aws-lc-rs's.
#[test]
#[allow(deprecated)]
fn digest_chaining_len() {
    use ours::digest as o;
    use theirs::digest as t;
    let pairs = [
        (&o::SHA1_FOR_LEGACY_USE_ONLY, &t::SHA1_FOR_LEGACY_USE_ONLY),
        (&o::SHA256, &t::SHA256),
        (&o::SHA384, &t::SHA384),
        (&o::SHA512, &t::SHA512),
    ];
    for (ours, theirs) in pairs {
        assert_eq!(ours.chaining_len(), theirs.chaining_len());
    }
}

/// Unequal slices compare unequal, as in aws-lc-rs.
#[test]
#[allow(deprecated)]
fn slices_compare() {
    for (a, b) in [
        (&b"abc"[..], &b"abc"[..]),
        (b"abc", b"abd"),
        (b"abc", b"ab"),
    ] {
        assert_eq!(
            ours::constant_time::verify_slices_are_equal(a, b).is_ok(),
            theirs::constant_time::verify_slices_are_equal(a, b).is_ok()
        );
    }
}

/// A randomized-nonce key draws a fresh nonce for each message.
#[test]
fn randomized_nonces_differ() {
    let key = ours::aead::RandomizedNonceKey::new(&ours::aead::AES_128_GCM, &[7; 16]).unwrap();
    let mut seal = || {
        let mut in_out = b"message".to_vec();
        *key.seal_in_place_append_tag(ours::aead::Aad::empty(), &mut in_out)
            .unwrap()
            .as_ref()
    };
    assert_ne!(seal(), seal());
}
