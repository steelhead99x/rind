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

    /// A key the module holds derives an empty `info` as aws-lc-rs does, with
    /// the same bytes, though the module refuses it: the adapter derives that
    /// in rind from a copy of the key. Every other `info` derives in the
    /// module, and the two agree with a key rind holds.
    #[test]
    fn hkdf_empty_info_follows_aws_lc_rs() {
        use ours::hkdf::{HKDF_SHA1_FOR_LEGACY_USE_ONLY, HKDF_SHA256, Prk, Salt};

        fn derive(prk: &Prk, info: &[&[u8]]) -> [u8; 42] {
            let mut out = [0u8; 42];
            let okm = prk.expand(info, Len(42)).unwrap();
            okm.fill(&mut out).unwrap();
            out
        }
        struct Len(usize);
        impl ours::hkdf::KeyType for Len {
            fn len(&self) -> usize {
                self.0
            }
        }

        let empty: &[&[u8]] = &[b""];
        let parts: &[&[u8]] = &[b"", b""];
        // A non-empty salt, extracted in the module.
        let module = Salt::new(HKDF_SHA256, b"a salt").extract(b"secret");
        assert!(module.expand(empty, HKDF_SHA256).is_ok());
        assert!(module.expand(&[b"info"], HKDF_SHA256).is_ok());
        let none: &[&[u8]] = &[];
        assert_eq!(derive(&module, empty), derive(&module, none));
        assert_eq!(derive(&module, empty), derive(&module, parts));
        // The same bytes as aws-lc-rs's HKDF, which derives it unapproved.
        let reference =
            aws_lc_rs::hkdf::Salt::new(aws_lc_rs::hkdf::HKDF_SHA256, b"a salt").extract(b"secret");
        struct RefLen(usize);
        impl aws_lc_rs::hkdf::KeyType for RefLen {
            fn len(&self) -> usize {
                self.0
            }
        }
        let mut expected = [0u8; 42];
        reference
            .expand(empty, RefLen(42))
            .unwrap()
            .fill(&mut expected)
            .unwrap();
        assert_eq!(derive(&module, empty), expected);
        // A key handed over whole is the module's too, and does the same.
        let given = Prk::new_less_safe(HKDF_SHA256, &[7; 32]);
        assert!(given.expand(empty, HKDF_SHA256).is_ok());
        assert_ne!(derive(&given, empty), derive(&given, &[b"info"]));
        // An absent salt and SHA-1 stay in rind, and expand any `info`.
        let rind = Salt::none(HKDF_SHA256).extract(b"secret");
        assert!(rind.expand(empty, HKDF_SHA256).is_ok());
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

    /// The module signs RSA-PSS only with a salt the hash's length, and its
    /// key cannot leave it, so another salt is refused; the default salt signs
    /// and verifies, and a salt the module does not take still verifies, in
    /// rind, since a public key holds no secret.
    #[test]
    fn rsa_signs_in_the_module_and_refuses_another_salt() {
        use ours::rsa::{KeyPair, KeySize, RsaPssSaltLength};
        use ours::signature::{
            KeyPair as _, RSA_PSS_2048_8192_SHA256, RSA_PSS_SHA256, UnparsedPublicKey,
        };

        const MAX: ours::signature::RsaSignatureEncoding =
            RSA_PSS_SHA256.with_pss_salt_length(RsaPssSaltLength::Max);
        let rng = ours::rand::SystemRandom::new();
        let key = KeyPair::generate(KeySize::Rsa2048).unwrap();
        let mut signature = vec![0; key.public_modulus_len()];
        key.sign(&RSA_PSS_SHA256, &rng, b"message", &mut signature)
            .unwrap();
        UnparsedPublicKey::new(&RSA_PSS_2048_8192_SHA256, key.public_key().as_ref())
            .verify(b"message", &signature)
            .unwrap();
        assert!(key.sign(&MAX, &rng, b"message", &mut signature).is_err());
    }

    /// X25519 stays in rind, and ECDH in the module; both agree.
    #[test]
    fn x25519_and_ecdh_both_agree() {
        use ours::agreement::{
            ECDH_P256, EphemeralPrivateKey, UnparsedPublicKey, X25519, agree_ephemeral,
        };

        let rng = ours::rand::SystemRandom::new();
        for algorithm in [&ECDH_P256, &X25519] {
            let a = EphemeralPrivateKey::generate(algorithm, &rng).unwrap();
            let b = EphemeralPrivateKey::generate(algorithm, &rng).unwrap();
            let (a_public, b_public) = (
                a.compute_public_key().unwrap(),
                b.compute_public_key().unwrap(),
            );
            let secret = |key, peer: &ours::agreement::PublicKey| {
                agree_ephemeral(
                    key,
                    UnparsedPublicKey::new(algorithm, peer.as_ref()),
                    (),
                    |secret| Ok(secret.to_vec()),
                )
                .unwrap()
            };
            assert_eq!(secret(a, &b_public), secret(b, &a_public));
        }
    }

    /// ML-KEM, AES key wrap, AES-CBC and AES-CTR, and QUIC header protection
    /// run in the module; ChaCha20 header protection, which the module does
    /// not approve, runs in rind.
    #[test]
    fn kem_key_wrap_cipher_and_quic_work_in_the_module() {
        use ours::aead::quic::{AES_128, CHACHA20, HeaderProtectionKey};
        use ours::cipher::{
            AES_128 as CIPHER_AES_128, DecryptionContext, PaddedBlockDecryptingKey,
            PaddedBlockEncryptingKey, UnboundCipherKey,
        };
        use ours::kem::{DecapsulationKey, ML_KEM_768};
        use ours::key_wrap::{AES_256, AesKek, KeyEncryptionKey, KeyWrap};

        let decapsulation = DecapsulationKey::generate(&ML_KEM_768).unwrap();
        let (ciphertext, secret) = decapsulation
            .encapsulation_key()
            .unwrap()
            .encapsulate()
            .unwrap();
        let opened = decapsulation.decapsulate(ciphertext).unwrap();
        assert_eq!(opened.as_ref(), secret.as_ref());

        let kek: AesKek = KeyEncryptionKey::new(&AES_256, &[3; 32]).unwrap();
        let mut wrapped = [0; 40];
        let wrapped = kek.wrap(&[9; 32], &mut wrapped).unwrap().to_vec();
        let kek: AesKek = KeyEncryptionKey::new(&AES_256, &[3; 32]).unwrap();
        let mut key = [0; 32];
        assert_eq!(kek.unwrap(&wrapped, &mut key).unwrap(), [9; 32]);

        let mut message = b"sixteen byte msg and a bit".to_vec();
        let unbound = || UnboundCipherKey::new(&CIPHER_AES_128, &[5; 16]).unwrap();
        let context = PaddedBlockEncryptingKey::cbc_pkcs7(unbound())
            .unwrap()
            .encrypt(&mut message)
            .unwrap();
        let context: DecryptionContext = context;
        let opened = PaddedBlockDecryptingKey::cbc_pkcs7(unbound())
            .unwrap()
            .decrypt(&mut message, context)
            .unwrap();
        assert_eq!(opened, b"sixteen byte msg and a bit");

        for (algorithm, len) in [(&AES_128, 16), (&CHACHA20, 32)] {
            let key = HeaderProtectionKey::new(algorithm, &vec![1; len]).unwrap();
            assert_eq!(key.new_mask(&[2; 16]).unwrap().len(), 5);
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
