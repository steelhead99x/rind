//! The `fips` feature: with it, the TLS record keys are held in rind-fips's
//! module, and `try_fips_mode()` fails until every approved service is; without
//! it, the keys run in rind and `try_fips_mode()` fails.

use ours::aead::{
    AES_128_GCM, Aad, Nonce, TlsProtocolId, TlsRecordOpeningKey, TlsRecordSealingKey,
};
use rind_aws_lc_rs as ours;

#[cfg(not(feature = "fips"))]
#[test]
fn without_the_feature_fips_mode_fails() {
    assert_eq!(ours::try_fips_mode(), Err("FIPS mode not enabled!"));
    assert_eq!(ours::fips_version(), None);
    // The keys still seal and open, and TLS 1.2 still seals.
    let mut key = TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS12, &[7; 16]).unwrap();
    let opening = TlsRecordOpeningKey::new(&AES_128_GCM, TlsProtocolId::TLS12, &[7; 16]).unwrap();
    let mut record = b"hello".to_vec();
    let nonce = Nonce::assume_unique_for_key([1; 12]);
    key.seal_in_place_append_tag(nonce, Aad::from(b"hdr"), &mut record)
        .unwrap();
    let nonce = Nonce::assume_unique_for_key([1; 12]);
    assert_eq!(
        opening
            .open_in_place(nonce, Aad::from(b"hdr"), &mut record)
            .unwrap(),
        b"hello"
    );
}

#[cfg(feature = "fips")]
mod with_the_feature {
    use ours::aead::{AES_256_GCM, CHACHA20_POLY1305};

    use super::*;

    /// TLS 1.3's nonce for sequence number `seq` under `iv`.
    fn nonce(iv: &[u8; 12], seq: u64) -> Nonce {
        let mut nonce = *iv;
        for (n, s) in nonce[4..].iter_mut().zip(seq.to_be_bytes()) {
            *n ^= s;
        }
        Nonce::assume_unique_for_key(nonce)
    }

    #[test]
    fn fips_mode_fails_while_services_still_run_in_rind() {
        // Reporting FIPS mode with approved services outside the module would
        // claim operations the module's boundary does not hold.
        let error = ours::try_fips_mode().unwrap_err();
        assert!(error.contains("still run in rind"), "{error}");
        // The module has no AWS-LC module number, and takes OS entropy.
        assert_eq!(ours::fips_version(), None);
        assert!(ours::try_fips_cpu_jitter_entropy().is_err());
    }

    /// A pseudorandom key the module holds refuses an empty `info`, which
    /// FIPS 140-3 does not approve; one rind holds expands it. So whether
    /// `expand` accepts an empty `info` shows where the key lives.
    #[test]
    fn hkdf_runs_in_the_module_where_it_is_approved() {
        use ours::hkdf::{HKDF_SHA1_FOR_LEGACY_USE_ONLY, HKDF_SHA256, Prk, Salt};

        let empty: &[&[u8]] = &[b""];
        // A non-empty salt, extracted in the module.
        let module = Salt::new(HKDF_SHA256, b"a salt").extract(b"secret");
        assert!(module.expand(empty, HKDF_SHA256).is_err());
        assert!(module.expand(&[b"info"], HKDF_SHA256).is_ok());
        // A key handed over whole is the module's too.
        let given = Prk::new_less_safe(HKDF_SHA256, &[7; 32]);
        assert!(given.expand(empty, HKDF_SHA256).is_err());
        // An absent salt is not approved, so the key stays in rind.
        let rind = Salt::none(HKDF_SHA256).extract(b"secret");
        assert!(rind.expand(empty, HKDF_SHA256).is_ok());
        // SHA-1 is not approved either.
        let sha1 = Salt::new(HKDF_SHA1_FOR_LEGACY_USE_ONLY, b"a salt").extract(b"secret");
        assert!(sha1.expand(empty, HKDF_SHA1_FOR_LEGACY_USE_ONLY).is_ok());
    }

    /// The module derives only what SP 800-132 approves; the rest still works,
    /// in rind, as in aws-lc-rs's FIPS build. Both give the same bytes as
    /// aws-lc-rs (tests/differential.rs); this checks they are both reachable.
    #[test]
    fn pbkdf2_derives_approved_and_unapproved_shapes() {
        use core::num::NonZeroU32;

        use ours::pbkdf2::{PBKDF2_HMAC_SHA256, derive, verify};

        let rounds = |n| NonZeroU32::new(n).unwrap();
        // Approved: a 14-byte secret, a 16-byte salt, 1000 rounds, 32 bytes.
        let mut approved = [0u8; 32];
        derive(
            PBKDF2_HMAC_SHA256,
            rounds(1000),
            &[1; 16],
            &[2; 14],
            &mut approved,
        );
        assert!(
            verify(
                PBKDF2_HMAC_SHA256,
                rounds(1000),
                &[1; 16],
                &[2; 14],
                &approved
            )
            .is_ok()
        );
        // Each unapproved shape still derives: a short salt, few rounds, a
        // short secret, a short output.
        for (rounds_, salt, secret, len) in [
            (1000, 8, 14, 32),
            (999, 16, 14, 32),
            (1000, 16, 13, 32),
            (1000, 16, 14, 13),
        ] {
            let mut out = vec![0u8; len];
            derive(
                PBKDF2_HMAC_SHA256,
                rounds(rounds_),
                &vec![1; salt],
                &vec![2; secret],
                &mut out,
            );
            assert!(
                out.iter().any(|&b| b != 0),
                "{rounds_} {salt} {secret} {len}"
            );
        }
    }

    #[test]
    fn a_sealed_record_opens_through_the_modules_opening_key() {
        let iv = [0x5a; 12];
        for (algorithm, key_bytes) in [(&AES_128_GCM, vec![9u8; 16]), (&AES_256_GCM, vec![9u8; 32])]
        {
            let mut sealing =
                TlsRecordSealingKey::new(algorithm, TlsProtocolId::TLS13, &key_bytes).unwrap();
            let opening =
                TlsRecordOpeningKey::new(algorithm, TlsProtocolId::TLS13, &key_bytes).unwrap();
            assert_eq!(sealing.tls_protocol_id(), TlsProtocolId::TLS13);
            assert_eq!(sealing.algorithm(), algorithm);
            for seq in [0u64, 1, 5] {
                let mut record = b"a TLS 1.3 record".to_vec();
                sealing
                    .seal_in_place_append_tag(nonce(&iv, seq), Aad::from(b"header"), &mut record)
                    .unwrap();
                assert_eq!(record.len(), 16 + 16);
                let plaintext = opening
                    .open_in_place(nonce(&iv, seq), Aad::from(b"header"), &mut record)
                    .unwrap();
                assert_eq!(plaintext, b"a TLS 1.3 record");
            }
        }
    }

    #[test]
    fn opening_refuses_a_wrong_nonce_aad_or_altered_record() {
        let iv = [3; 12];
        let mut sealing =
            TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[1; 16]).unwrap();
        let opening =
            TlsRecordOpeningKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[1; 16]).unwrap();
        let mut sealed = b"secret".to_vec();
        sealing
            .seal_in_place_append_tag(nonce(&iv, 0), Aad::from(b"h"), &mut sealed)
            .unwrap();
        for (seq, aad, flip) in [(1u64, &b"h"[..], false), (0, b"x", false), (0, b"h", true)] {
            let mut copy = sealed.clone();
            if flip {
                copy[0] ^= 1;
            }
            assert!(
                opening
                    .open_in_place(nonce(&iv, seq), Aad::from(aad), &mut copy)
                    .is_err(),
                "seq {seq}, aad {aad:?}, flip {flip}"
            );
        }
        // A record shorter than a tag fails, and so does a range past the end.
        assert!(
            opening
                .open_in_place(nonce(&iv, 0), Aad::from(b"h"), &mut [0u8; 3])
                .is_err()
        );
        assert!(
            opening
                .open_within(nonce(&iv, 0), Aad::from(b"h"), &mut sealed.clone(), 99..)
                .is_err()
        );
    }

    #[test]
    fn open_within_moves_the_plaintext_to_the_front() {
        let iv = [4; 12];
        let mut sealing =
            TlsRecordSealingKey::new(&AES_256_GCM, TlsProtocolId::TLS13, &[2; 32]).unwrap();
        let opening =
            TlsRecordOpeningKey::new(&AES_256_GCM, TlsProtocolId::TLS13, &[2; 32]).unwrap();
        let mut record = b"payload".to_vec();
        sealing
            .seal_in_place_append_tag(nonce(&iv, 0), Aad::from(b""), &mut record)
            .unwrap();
        let mut framed = b"HEADER".to_vec();
        framed.extend_from_slice(&record);
        let plaintext = opening
            .open_within(nonce(&iv, 0), Aad::from(b""), &mut framed, 6..)
            .unwrap();
        assert_eq!(plaintext, b"payload");
    }

    #[test]
    fn sealing_refuses_a_repeated_or_lower_sequence_number() {
        let iv = [6; 12];
        let mut sealing =
            TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[1; 16]).unwrap();
        let mut seal = |seq| {
            let mut record = b"x".to_vec();
            let result =
                sealing.seal_in_place_append_tag(nonce(&iv, seq), Aad::from(b""), &mut record);
            (result, record)
        };
        // The first nonce is the IV itself, sequence number 0.
        assert!(seal(0).0.is_ok());
        // A repeat is refused, leaving no plaintext behind.
        let (result, record) = seal(0);
        assert!(result.is_err());
        assert!(record.iter().take(1).all(|byte| *byte == 0));
        // Later numbers may skip ahead, but never go back.
        assert!(seal(5).0.is_ok());
        assert!(seal(2).0.is_err());
        assert!(seal(6).0.is_ok());
    }

    #[test]
    fn the_scatter_form_matches_the_in_place_form() {
        let iv = [8; 12];
        let key_bytes = [5u8; 16];
        let mut scatter =
            TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &key_bytes).unwrap();
        let mut in_place =
            TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &key_bytes).unwrap();
        let (head, extra) = (b"first part".as_slice(), b"and the extra".as_slice());
        let mut ciphertext = vec![0u8; head.len()];
        let mut extra_and_tag = vec![0u8; extra.len() + 16];
        scatter
            .seal_out_of_place_scatter(
                nonce(&iv, 0),
                Aad::from(b"aad"),
                head,
                &mut ciphertext,
                extra,
                &mut extra_and_tag,
            )
            .unwrap();
        let mut whole = [head, extra].concat();
        let tag = in_place
            .seal_in_place_separate_tag(nonce(&iv, 0), Aad::from(b"aad"), &mut whole)
            .unwrap();
        assert_eq!(ciphertext, whole[..head.len()]);
        assert_eq!(extra_and_tag[..extra.len()], whole[head.len()..]);
        assert_eq!(extra_and_tag[extra.len()..], *tag.as_ref());
        // Mismatched buffers are refused before the nonce is spent.
        let mut short = vec![0u8; 3];
        assert!(
            scatter
                .seal_out_of_place_scatter(
                    nonce(&iv, 1),
                    Aad::from(b"aad"),
                    head,
                    &mut short,
                    extra,
                    &mut extra_and_tag,
                )
                .is_err()
        );
    }

    #[test]
    fn what_the_module_does_not_seal_is_refused() {
        // The module seals only TLS 1.3 records, with AES-GCM.
        assert!(TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS12, &[1; 16]).is_err());
        assert!(
            TlsRecordSealingKey::new(&CHACHA20_POLY1305, TlsProtocolId::TLS13, &[1; 32]).is_err()
        );
        assert!(TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[1; 15]).is_err());
        // Opening takes either version, which checks nothing a plain AES-GCM
        // open does not.
        assert!(TlsRecordOpeningKey::new(&AES_128_GCM, TlsProtocolId::TLS12, &[1; 16]).is_ok());
        assert!(
            TlsRecordOpeningKey::new(&CHACHA20_POLY1305, TlsProtocolId::TLS13, &[1; 32]).is_err()
        );
    }

    #[test]
    fn debug_output_names_no_key_bytes() {
        let sealing =
            TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[0xab; 16]).unwrap();
        let opening =
            TlsRecordOpeningKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[0xab; 16]).unwrap();
        for text in [format!("{sealing:?}"), format!("{opening:?}")] {
            assert!(!text.to_lowercase().contains("abab"), "{text}");
        }
    }
}
