//! The compositions rind-ring builds itself, HKDF on rind's HMAC and the
//! short PBKDF2 compare, checked against aws-lc-rs, whose names match ring's.

// aws-lc-rs does not build for wasm.
#![cfg(not(target_family = "wasm"))]

use core::num::NonZeroU32;

use aws_lc_rs as theirs;
use proptest::collection::vec;
use proptest::prelude::*;
use rind_ring as ours;

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

fn hkdf_algorithms() -> [(ours::hkdf::Algorithm, theirs::hkdf::Algorithm, usize); 4] {
    [
        (
            ours::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
            theirs::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
            20,
        ),
        (ours::hkdf::HKDF_SHA256, theirs::hkdf::HKDF_SHA256, 32),
        (ours::hkdf::HKDF_SHA384, theirs::hkdf::HKDF_SHA384, 48),
        (ours::hkdf::HKDF_SHA512, theirs::hkdf::HKDF_SHA512, 64),
    ]
}

// Salts either side of both block sizes (64 and 128), info split into parts,
// and lengths from empty up to a few blocks, or either side of each hash's
// 255-block limit.
proptest! {
    #[test]
    fn hkdf_expand(
        algorithm in 0..4usize,
        salt in vec(any::<u8>(), 0..200),
        ikm in vec(any::<u8>(), 0..200),
        info in vec(vec(any::<u8>(), 0..100), 0..4),
        len in 0..200usize,
        at_limit in any::<bool>(),
    ) {
        let (ours_alg, theirs_alg, hash_len) = hkdf_algorithms()[algorithm];
        let len = match at_limit {
            true => 255 * hash_len + len - 100,
            false => len,
        };
        let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();

        let ours_prk = ours::hkdf::Salt::new(ours_alg, &salt).extract(&ikm);
        let theirs_prk = theirs::hkdf::Salt::new(theirs_alg, &salt).extract(&ikm);
        match (ours_prk.expand(&info, Len(len)), theirs_prk.expand(&info, Len(len))) {
            (Ok(ours_okm), Ok(theirs_okm)) => {
                let mut ours_out = vec![0u8; len];
                ours_okm.fill(&mut ours_out).unwrap();
                let mut theirs_out = vec![0u8; len];
                theirs_okm.fill(&mut theirs_out).unwrap();
                prop_assert_eq!(ours_out, theirs_out);
            }
            (Err(_), Err(_)) => {}
            (ours_result, theirs_result) => prop_assert!(
                false,
                "rind-ring {:?}, aws-lc-rs {:?}",
                ours_result.is_ok(),
                theirs_result.is_ok()
            ),
        }
    }

    // Each key an `Okm` becomes, a PRK taken as is, and a PRK or salt made
    // from an `Okm`, compared by what they then produce.
    #[test]
    fn hkdf_keys(
        algorithm in 0..4usize,
        ikm in vec(any::<u8>(), 0..100),
        info in vec(vec(any::<u8>(), 0..50), 0..3),
        msg in vec(any::<u8>(), 0..100),
    ) {
        let (ours_alg, theirs_alg, hash_len) = hkdf_algorithms()[algorithm];
        let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();
        let ours_prk = ours::hkdf::Salt::new(ours_alg, b"salt").extract(&ikm);
        let theirs_prk = theirs::hkdf::Salt::new(theirs_alg, b"salt").extract(&ikm);

        for (ours_aead, theirs_aead) in [
            (&ours::aead::AES_128_GCM, &theirs::aead::AES_128_GCM),
            (&ours::aead::AES_256_GCM, &theirs::aead::AES_256_GCM),
            (&ours::aead::CHACHA20_POLY1305, &theirs::aead::CHACHA20_POLY1305),
        ] {
            let ours_key = ours::aead::LessSafeKey::new(ours::aead::UnboundKey::from(
                ours_prk.expand(&info, ours_aead).unwrap(),
            ));
            let mut ours_sealed = msg.clone();
            ours_key
                .seal_in_place_append_tag(
                    ours::aead::Nonce::assume_unique_for_key([0; 12]),
                    ours::aead::Aad::empty(),
                    &mut ours_sealed,
                )
                .unwrap();

            let theirs_key = theirs::aead::LessSafeKey::new(theirs::aead::UnboundKey::from(
                theirs_prk.expand(&info, theirs_aead).unwrap(),
            ));
            let mut theirs_sealed = msg.clone();
            theirs_key
                .seal_in_place_append_tag(
                    theirs::aead::Nonce::assume_unique_for_key([0; 12]),
                    theirs::aead::Aad::empty(),
                    &mut theirs_sealed,
                )
                .unwrap();
            prop_assert_eq!(ours_sealed, theirs_sealed);
        }

        for (ours_quic, theirs_quic) in [
            (&ours::aead::quic::AES_128, &theirs::aead::quic::AES_128),
            (&ours::aead::quic::AES_256, &theirs::aead::quic::AES_256),
            (&ours::aead::quic::CHACHA20, &theirs::aead::quic::CHACHA20),
        ] {
            let sample = [0x5a; 16];
            let ours_key = ours::aead::quic::HeaderProtectionKey::from(
                ours_prk.expand(&info, ours_quic).unwrap(),
            );
            let theirs_key = theirs::aead::quic::HeaderProtectionKey::from(
                theirs_prk.expand(&info, theirs_quic).unwrap(),
            );
            prop_assert_eq!(
                ours_key.new_mask(&sample).unwrap(),
                theirs_key.new_mask(&sample).unwrap()
            );
        }

        let ours_hmac = ours_alg.hmac_algorithm();
        let theirs_hmac = theirs_alg.hmac_algorithm();
        let ours_key = ours::hmac::Key::from(ours_prk.expand(&info, ours_hmac).unwrap());
        let theirs_key = theirs::hmac::Key::from(theirs_prk.expand(&info, theirs_hmac).unwrap());
        let ours_tag = ours::hmac::sign(&ours_key, &msg);
        let theirs_tag = theirs::hmac::sign(&theirs_key, &msg);
        prop_assert_eq!(ours_tag.as_ref(), theirs_tag.as_ref());

        let ours_next = ours::hkdf::Prk::from(ours_prk.expand(&info, ours_alg).unwrap());
        let theirs_next = theirs::hkdf::Prk::from(theirs_prk.expand(&info, theirs_alg).unwrap());
        let ours_salt = ours::hkdf::Salt::from(ours_prk.expand(&info, ours_alg).unwrap());
        let theirs_salt = theirs::hkdf::Salt::from(theirs_prk.expand(&info, theirs_alg).unwrap());
        // aws-lc-rs panics on a PRK longer than a hash output; ring and
        // rind-ring take any length.
        let raw = &msg[..msg.len().min(hash_len)];
        let ours_raw = ours::hkdf::Prk::new_less_safe(ours_alg, raw);
        let theirs_raw = theirs::hkdf::Prk::new_less_safe(theirs_alg, raw);
        for (ours_prk, theirs_prk) in [
            (ours_next, theirs_next),
            (ours_salt.extract(&msg), theirs_salt.extract(&msg)),
            (ours_raw, theirs_raw),
        ] {
            let mut ours_out = [0u8; 100];
            ours_prk.expand(&info, Len(100)).unwrap().fill(&mut ours_out).unwrap();
            let mut theirs_out = [0u8; 100];
            theirs_prk.expand(&info, Len(100)).unwrap().fill(&mut theirs_out).unwrap();
            prop_assert_eq!(ours_out, theirs_out);
        }
    }

    // Stored values from empty to a few blocks, including those shorter than
    // the hash, which rind-ring compares itself, and a corrupted byte.
    #[test]
    fn pbkdf2_verify(
        password in vec(any::<u8>(), 0..100),
        salt in vec(any::<u8>(), 0..100),
        iterations in 1..5u32,
        len in 0..150usize,
        corrupt in any::<prop::sample::Index>(),
    ) {
        let iterations = NonZeroU32::new(iterations).unwrap();
        for (ours_alg, theirs_alg) in [
            (ours::pbkdf2::PBKDF2_HMAC_SHA1, theirs::pbkdf2::PBKDF2_HMAC_SHA1),
            (ours::pbkdf2::PBKDF2_HMAC_SHA256, theirs::pbkdf2::PBKDF2_HMAC_SHA256),
            (ours::pbkdf2::PBKDF2_HMAC_SHA384, theirs::pbkdf2::PBKDF2_HMAC_SHA384),
            (ours::pbkdf2::PBKDF2_HMAC_SHA512, theirs::pbkdf2::PBKDF2_HMAC_SHA512),
        ] {
            let mut stored = vec![0u8; len];
            theirs::pbkdf2::derive(theirs_alg, iterations, &salt, &password, &mut stored);
            let mut derived = vec![0u8; len];
            ours::pbkdf2::derive(ours_alg, iterations, &salt, &password, &mut derived);
            prop_assert_eq!(&derived, &stored);

            let verify = |stored: &[u8]| {
                (
                    ours::pbkdf2::verify(ours_alg, iterations, &salt, &password, stored).is_ok(),
                    theirs::pbkdf2::verify(theirs_alg, iterations, &salt, &password, stored)
                        .is_ok(),
                )
            };
            let (ours_ok, theirs_ok) = verify(&stored);
            prop_assert_eq!(ours_ok, theirs_ok);
            if !stored.is_empty() {
                stored[corrupt.index(len)] ^= 1;
                prop_assert_eq!(verify(&stored), (false, false));
            }
        }
    }
}
