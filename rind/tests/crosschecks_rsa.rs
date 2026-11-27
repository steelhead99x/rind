//! Differential tests of RSA and RFC 9474's blind RSA against aws-lc and
//! independent oracles, which Miri cannot run.
#![cfg(not(any(miri, target_family = "wasm")))]

mod common;
use common::der;

mod rsa {
    use std::sync::LazyLock;

    use ::rsa::pkcs1::DecodeRsaPublicKey;
    use ::rsa::pkcs8::{DecodePrivateKey, EncodePrivateKey, EncodePublicKey};
    use aws_lc_rs::encoding::AsDer;
    use aws_lc_rs::rand::SystemRandom;
    use aws_lc_rs::rsa::{KeyPair, KeySize};
    use aws_lc_rs::signature::RsaPssSaltLength as TheirsSaltLength;
    use aws_lc_rs::signature::{self, KeyPair as _, UnparsedPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::Error;
    use rind::rsa::{
        KeyPair as RsaKeyPair, PssSaltLength as RsaPssSaltLength,
        SigningAlgorithm as RsaSigningAlgorithm, VerificationAlgorithm as RsaVerificationAlgorithm,
        sign, verify,
    };

    /// One padding and hash: each side's signing and verification constants.
    struct Scheme {
        ours_sign: &'static RsaSigningAlgorithm,
        ours_verify: &'static RsaVerificationAlgorithm,
        theirs_sign: &'static signature::RsaSignatureEncoding,
        theirs_verify: &'static signature::RsaParameters,
        /// PKCS#1 v1.5 signatures have no randomness, so both sides must agree.
        deterministic: bool,
        /// RustCrypto's signature under the scheme, and its verdict on one.
        oracle_sign: fn(&::rsa::PrivateKey, &[u8]) -> Vec<u8>,
        oracle_verify: Oracle,
    }

    const SCHEMES: [Scheme; 6] = [
        Scheme {
            ours_sign: &sign::PKCS1_SHA256,
            ours_verify: &verify::PKCS1_SHA256,
            theirs_sign: &signature::RSA_PKCS1_SHA256,
            theirs_verify: &signature::RSA_PKCS1_2048_8192_SHA256,
            deterministic: true,
            oracle_sign: |key, message| key.pkcs1v15_sign::<::sha2::Sha256>(message).unwrap(),
            oracle_verify: pkcs1::<::sha2::Sha256>,
        },
        Scheme {
            ours_sign: &sign::PKCS1_SHA384,
            ours_verify: &verify::PKCS1_SHA384,
            theirs_sign: &signature::RSA_PKCS1_SHA384,
            theirs_verify: &signature::RSA_PKCS1_2048_8192_SHA384,
            deterministic: true,
            oracle_sign: |key, message| key.pkcs1v15_sign::<::sha2::Sha384>(message).unwrap(),
            oracle_verify: pkcs1::<::sha2::Sha384>,
        },
        Scheme {
            ours_sign: &sign::PKCS1_SHA512,
            ours_verify: &verify::PKCS1_SHA512,
            theirs_sign: &signature::RSA_PKCS1_SHA512,
            theirs_verify: &signature::RSA_PKCS1_2048_8192_SHA512,
            deterministic: true,
            oracle_sign: |key, message| key.pkcs1v15_sign::<::sha2::Sha512>(message).unwrap(),
            oracle_verify: pkcs1::<::sha2::Sha512>,
        },
        Scheme {
            ours_sign: &sign::PSS_SHA256,
            ours_verify: &verify::PSS_SHA256,
            theirs_sign: &signature::RSA_PSS_SHA256,
            theirs_verify: &signature::RSA_PSS_2048_8192_SHA256,
            deterministic: false,
            oracle_sign: |key, message| key.pss_sign::<::sha2::Sha256>(message).unwrap(),
            oracle_verify: pss::<::sha2::Sha256>,
        },
        Scheme {
            ours_sign: &sign::PSS_SHA384,
            ours_verify: &verify::PSS_SHA384,
            theirs_sign: &signature::RSA_PSS_SHA384,
            theirs_verify: &signature::RSA_PSS_2048_8192_SHA384,
            deterministic: false,
            oracle_sign: |key, message| key.pss_sign::<::sha2::Sha384>(message).unwrap(),
            oracle_verify: pss::<::sha2::Sha384>,
        },
        Scheme {
            ours_sign: &sign::PSS_SHA512,
            ours_verify: &verify::PSS_SHA512,
            theirs_sign: &signature::RSA_PSS_SHA512,
            theirs_verify: &signature::RSA_PSS_2048_8192_SHA512,
            deterministic: false,
            oracle_sign: |key, message| key.pss_sign::<::sha2::Sha512>(message).unwrap(),
            oracle_verify: pss::<::sha2::Sha512>,
        },
    ];

    #[test]
    fn key_generation_2048() {
        check_key_generation(rind::rsa::KeySize::Rsa2048);
    }

    #[test]
    fn key_generation_2048_soak() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            for _ in 0..512 {
                check_key_generation(rind::rsa::KeySize::Rsa2048);
            }
        }
    }

    #[test]
    fn key_generation_3072() {
        check_key_generation(rind::rsa::KeySize::Rsa3072);
    }

    #[test]
    fn key_generation_4096() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            check_key_generation(rind::rsa::KeySize::Rsa4096);
        }
    }

    #[test]
    fn key_generation_6144() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            check_key_generation(rind::rsa::KeySize::Rsa6144);
        }
    }

    #[test]
    fn key_generation_8192() {
        if std::env::var_os("SLOW_TESTS").is_some() {
            check_key_generation(rind::rsa::KeySize::Rsa8192);
        }
    }

    /// aws-lc-rs and RustCrypto accept a key we generate and verify its
    /// signatures under every scheme, as we do.
    fn check_key_generation(size: rind::rsa::KeySize) {
        let ours = RsaKeyPair::generate(size).unwrap();
        let theirs = KeyPair::from_pkcs8(ours.to_pkcs8().as_ref())
            .expect("aws-lc-rs rejected a key we generated");
        let oracle = ::rsa::PrivateKey::from_pkcs8_der(ours.to_pkcs8().as_ref())
            .expect("RustCrypto rejected a key we generated");
        oracle.validate().unwrap();
        let public = theirs.public_key().as_ref();
        for scheme in &SCHEMES {
            let signature = ours.sign(scheme.ours_sign, b"hello").unwrap();
            UnparsedPublicKey::new(scheme.theirs_verify, public)
                .verify(b"hello", signature.as_ref())
                .unwrap();
            assert!((scheme.oracle_verify)(
                oracle.as_public_key(),
                b"hello",
                signature.as_ref()
            ));
            rind::rsa::PublicKey::new(public)
                .unwrap()
                .verify(scheme.ours_verify, b"hello", signature.as_ref())
                .unwrap();
        }
    }

    // Loaded by both: one key generated by aws-lc-rs (`check_key_generation`
    // covers the reverse), and OpenSSL keys aws-lc-rs cannot generate: moduli
    // that are not a whole number of words, and a 33-bit public exponent,
    // 2^32 + 1. At 2049 bits PSS's encoded message is a byte shorter than the
    // modulus, at 2050 bits it masks seven top bits, and 2056 bits is a whole
    // number of bytes. Key generation is slow under emulation, so there is
    // one of each.
    static THEIRS: LazyLock<[KeyPair; 5]> = LazyLock::new(|| {
        [
            KeyPair::generate(KeySize::Rsa2048).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2049.pkcs8.der")).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2050.pkcs8.der")).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2056.pkcs8.der")).unwrap(),
            KeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2048-e33.pkcs8.der")).unwrap(),
        ]
    });

    // Each case makes a dozen private-key operations per key, which are slow
    // under emulation.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8))]

        #[test]
        fn sign_verify(message in vec(any::<u8>(), 0..300)) {
            for theirs in &*THEIRS {
                let ours = RsaKeyPair::from_pkcs8(theirs.as_der().unwrap().as_ref()).unwrap();
                let public = theirs.public_key().as_ref();
                let spki = theirs.public_key().as_der().unwrap();
                let ours_spki = ours.public_key().to_spki();
                prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
                // RustCrypto reads our PKCS#8 to the same public key.
                let oracle = ::rsa::PrivateKey::from_pkcs8_der(ours.to_pkcs8().as_ref()).unwrap();
                let oracle_spki = oracle.to_public_key().to_public_key_der().unwrap();
                prop_assert_eq!(oracle_spki.as_bytes(), ours_spki.as_ref());
                let rng = SystemRandom::new();
                let len = theirs.public_modulus_len();
                prop_assert_eq!(ours.public_key().modulus_len(), len);

                for scheme in &SCHEMES {
                    prop_assert_eq!(ours.public_key().as_ref(), public);

                    // Both verify our signature.
                    let ours_signature = ours.sign(scheme.ours_sign, &message).unwrap();
                    let ours_signature = ours_signature.as_ref();
                    prop_assert_eq!(ours_signature.len(), len);
                    UnparsedPublicKey::new(scheme.theirs_verify, public)
                        .verify(&message, ours_signature)
                        .unwrap();
                    prop_assert!((scheme.oracle_verify)(
                        oracle.as_public_key(),
                        &message,
                        ours_signature
                    ));

                    // We verify its signature, and refuse it over another message.
                    let mut theirs_signature = vec![0u8; len];
                    theirs
                        .sign(scheme.theirs_sign, &rng, &message, &mut theirs_signature)
                        .unwrap();
                    if scheme.deterministic {
                        prop_assert_eq!(ours_signature, &theirs_signature[..]);
                    }
                    let verifier = rind::rsa::PublicKey::new(public).unwrap();
                    let verifier_spki = verifier.to_spki();
                    prop_assert_eq!(verifier_spki.as_ref(), spki.as_ref());
                    verifier.verify(scheme.ours_verify, &message, &theirs_signature).unwrap();
                    prop_assert_eq!(
                        verifier.verify(
                            scheme.ours_verify,
                            &[&message[..], b"!"].concat(),
                            &theirs_signature,
                        ),
                        Err(Error::BadSignature)
                    );

                    // And RustCrypto's.
                    let oracle_signature = (scheme.oracle_sign)(&oracle, &message);
                    if scheme.deterministic {
                        prop_assert_eq!(ours_signature, &oracle_signature[..]);
                    }
                    verifier.verify(scheme.ours_verify, &message, &oracle_signature).unwrap();
                }
            }
        }
    }

    /// One PSS hash with a chosen salt length: each side's constructor.
    struct PssSalt {
        ours_sign: fn(RsaPssSaltLength) -> RsaSigningAlgorithm,
        ours_verify: fn(RsaPssSaltLength) -> RsaVerificationAlgorithm,
        ours_any_salt: &'static RsaVerificationAlgorithm,
        theirs_sign: fn(TheirsSaltLength) -> signature::RsaSignatureEncoding,
        theirs_verify: fn(TheirsSaltLength) -> signature::RsaParameters,
        /// RustCrypto's signature with a salt of the given length, and its
        /// verdict on one.
        oracle_sign: fn(&::rsa::PrivateKey, &[u8], usize) -> Vec<u8>,
        oracle_verify: fn(&::rsa::PublicKey, &[u8], &[u8], usize) -> bool,
        hash_len: usize,
    }

    fn pss_salt_sign<D: ::sha2::Digest + ::sha2::digest::FixedOutputReset>(
        key: &::rsa::PrivateKey,
        message: &[u8],
        salt: usize,
    ) -> Vec<u8> {
        let padding = ::rsa::pss::Pss::<D>::new_with_salt(salt);
        key.sign_with_rng(&mut getrandom::SysRng, padding, &D::digest(message))
            .unwrap()
    }

    fn pss_salt_verify<D: ::sha2::Digest + ::sha2::digest::FixedOutputReset>(
        key: &::rsa::PublicKey,
        message: &[u8],
        signature: &[u8],
        salt: usize,
    ) -> bool {
        let padding = ::rsa::pss::Pss::<D>::new_with_salt(salt);
        key.verify(padding, &D::digest(message), signature).is_ok()
    }

    const PSS_SALTS: [PssSalt; 3] = [
        PssSalt {
            ours_sign: RsaSigningAlgorithm::pss_sha256,
            ours_verify: RsaVerificationAlgorithm::pss_sha256,
            ours_any_salt: &verify::PSS_SHA256_ANY_SALT,
            theirs_sign: |salt| signature::RSA_PSS_SHA256.with_pss_salt_length(salt),
            theirs_verify: |salt| signature::RSA_PSS_2048_8192_SHA256.with_pss_salt_length(salt),
            oracle_sign: pss_salt_sign::<::sha2::Sha256>,
            oracle_verify: pss_salt_verify::<::sha2::Sha256>,
            hash_len: 32,
        },
        PssSalt {
            ours_sign: RsaSigningAlgorithm::pss_sha384,
            ours_verify: RsaVerificationAlgorithm::pss_sha384,
            ours_any_salt: &verify::PSS_SHA384_ANY_SALT,
            theirs_sign: |salt| signature::RSA_PSS_SHA384.with_pss_salt_length(salt),
            theirs_verify: |salt| signature::RSA_PSS_2048_8192_SHA384.with_pss_salt_length(salt),
            oracle_sign: pss_salt_sign::<::sha2::Sha384>,
            oracle_verify: pss_salt_verify::<::sha2::Sha384>,
            hash_len: 48,
        },
        PssSalt {
            ours_sign: RsaSigningAlgorithm::pss_sha512,
            ours_verify: RsaVerificationAlgorithm::pss_sha512,
            ours_any_salt: &verify::PSS_SHA512_ANY_SALT,
            theirs_sign: |salt| signature::RSA_PSS_SHA512.with_pss_salt_length(salt),
            theirs_verify: |salt| signature::RSA_PSS_2048_8192_SHA512.with_pss_salt_length(salt),
            oracle_sign: pss_salt_sign::<::sha2::Sha512>,
            oracle_verify: pss_salt_verify::<::sha2::Sha512>,
            hash_len: 64,
        },
    ];

    // As `sign_verify`, a dozen private-key operations per key per case.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(8))]

        /// Each side verifies the other's PSS signatures with any salt length
        /// the modulus allows, as does any-salt verification, and both refuse
        /// one a byte longer.
        #[test]
        fn pss_salt_lengths(salt in any::<u16>(), message in vec(any::<u8>(), 0..300)) {
            for theirs in &*THEIRS {
                let ours = RsaKeyPair::from_pkcs8(theirs.as_der().unwrap().as_ref()).unwrap();
                let public = theirs.public_key().as_ref();
                let bits = signature::RsaParameters::public_modulus_len(public).unwrap() as usize;
                let rng = SystemRandom::new();

                for pss in &PSS_SALTS {
                    let ours_public = rind::rsa::PublicKey::new(public).unwrap();
                    // RFC 8017 section 9.1.1's `emLen - hLen - 2`.
                    let max = u16::try_from((bits - 1).div_ceil(8) - pss.hash_len - 2).unwrap();
                    let custom = salt % (max + 1);

                    for (ours_salt, theirs_salt) in [
                        (RsaPssSaltLength::Custom(custom), TheirsSaltLength::Custom(custom)),
                        (RsaPssSaltLength::Max, TheirsSaltLength::Max),
                        (RsaPssSaltLength::Custom(max + 1), TheirsSaltLength::Custom(max + 1)),
                    ] {
                        // aws-lc-rs takes only `'static` algorithms.
                        let theirs_sign = Box::leak(Box::new((pss.theirs_sign)(theirs_salt)));
                        let theirs_verify = Box::leak(Box::new((pss.theirs_verify)(theirs_salt)));
                        let ours_sign = (pss.ours_sign)(ours_salt);
                        let ours_verify = (pss.ours_verify)(ours_salt);

                        let mut theirs_signature = vec![0u8; theirs.public_modulus_len()];
                        let theirs_signed =
                            theirs.sign(theirs_sign, &rng, &message, &mut theirs_signature);
                        if ours_salt == RsaPssSaltLength::Custom(max + 1) {
                            prop_assert!(theirs_signed.is_err());
                            prop_assert!(matches!(
                                ours.sign(&ours_sign, &message),
                                Err(Error::KeyRejected(_))
                            ));
                            prop_assert!(matches!(
                                ours_public.verify(&ours_verify, &message, &theirs_signature),
                                Err(Error::KeyRejected(_))
                            ));
                            continue;
                        }
                        theirs_signed.unwrap();
                        let other_message = [&message[..], b"!"].concat();
                        for verifier in [&ours_verify, pss.ours_any_salt] {
                            ours_public.verify(verifier, &message, &theirs_signature).unwrap();
                            prop_assert_eq!(
                                ours_public.verify(verifier, &other_message, &theirs_signature),
                                Err(Error::BadSignature)
                            );
                        }

                        let ours_signature = ours.sign(&ours_sign, &message).unwrap();
                        UnparsedPublicKey::new(theirs_verify, public)
                            .verify(&message, ours_signature.as_ref())
                            .unwrap();
                        ours.public_key()
                            .verify(&ours_verify, &message, ours_signature.as_ref())
                            .unwrap();
                    }
                }
            }
        }
    }

    /// RustCrypto and rind verify each other's PSS signatures with no salt,
    /// a salt not the hash's length, and the longest the modulus allows,
    /// and rind refuses each with a salt a byte shorter or longer.
    #[test]
    fn pss_salt_lengths_oracle() {
        // A whole number of bytes, and one bit past, where PSS's encoded
        // message is a byte shorter than the modulus.
        for theirs in &THEIRS[..2] {
            let pkcs8 = theirs.as_der().unwrap();
            let ours = RsaKeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
            let oracle = ::rsa::PrivateKey::from_pkcs8_der(pkcs8.as_ref()).unwrap();
            let public = ours.public_key();
            let bits = signature::RsaParameters::public_modulus_len(theirs.public_key().as_ref())
                .unwrap() as usize;
            let message = b"hello";
            for pss in &PSS_SALTS {
                // RFC 8017 section 9.1.1's `emLen - hLen - 2`.
                let max = (bits - 1).div_ceil(8) - pss.hash_len - 2;
                for salt in [0, pss.hash_len - 1, max] {
                    let with = |len: usize| {
                        (pss.ours_verify)(RsaPssSaltLength::Custom(len.try_into().unwrap()))
                    };
                    let signature = (pss.oracle_sign)(&oracle, message, salt);
                    public.verify(&with(salt), message, &signature).unwrap();
                    public
                        .verify(pss.ours_any_salt, message, &signature)
                        .unwrap();
                    if salt > 0 {
                        assert_eq!(
                            public.verify(&with(salt - 1), message, &signature),
                            Err(Error::BadSignature)
                        );
                    }
                    if salt < max {
                        assert_eq!(
                            public.verify(&with(salt + 1), message, &signature),
                            Err(Error::BadSignature)
                        );
                    }

                    let ours_sign =
                        (pss.ours_sign)(RsaPssSaltLength::Custom(salt.try_into().unwrap()));
                    let signature = ours.sign(&ours_sign, message).unwrap();
                    assert!((pss.oracle_verify)(
                        oracle.as_public_key(),
                        message,
                        signature.as_ref(),
                        salt
                    ));
                    if salt > 0 {
                        assert!(!(pss.oracle_verify)(
                            oracle.as_public_key(),
                            message,
                            signature.as_ref(),
                            salt - 1
                        ));
                    }
                }
            }
        }
    }

    // Each case loads every key twice and signs with each one that loads.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        /// aws-lc-rs and rind load a key from its integers, or refuse it,
        /// alike, whichever one is altered: with a leading zero byte, a
        /// flipped bit, or a byte cut off. RustCrypto, which takes only n, e,
        /// d, and the primes and derives the rest, loads every key rind does
        /// to the same PKCS#8 and PKCS#1 v1.5 signature, and refuses every
        /// one rind does whose change it sees.
        #[test]
        fn from_components(field in 0..8usize, change in 0..4u8, at in any::<prop::sample::Index>()) {
            for theirs in &*THEIRS {
                let pkcs8 = theirs.as_der().unwrap();
                let mut fields = components(pkcs8.as_ref());
                let value = &mut fields[field];
                match change {
                    0 => {}
                    1 => value.insert(0, 0),
                    2 => {
                        let i = at.index(value.len());
                        value[i] ^= 1 << (i % 8);
                    }
                    _ => {
                        value.pop();
                    }
                }
                let [n, e, d, p, q, dp, dq, qi] = &fields[..] else { unreachable!() };
                let ours = RsaKeyPair::from_components(&rind::rsa::KeyPairComponents {
                    public_key: rind::rsa::PublicKeyComponents { n, e },
                    d, p, q, dp, dq, qi,
                });
                let them = KeyPair::from_components(&aws_lc_rs::rsa::KeyPairComponents {
                    public_key: aws_lc_rs::rsa::PublicKeyComponents { n, e },
                    d, p, q, dP: dp, dQ: dq, qInv: qi,
                });
                prop_assert_eq!(ours.is_ok(), them.is_ok(), "field {} change {}", field, change);
                let int = |x: &[u8]| ::rsa::BoxedUint::from_be_slice_vartime(x);
                let oracle = ::rsa::PrivateKey::from_components(
                    int(n), int(e), int(d), vec![int(p), int(q)],
                );
                // RustCrypto reads n and e as numbers, and derives dP, dQ,
                // and qInv, so it cannot see a leading zero there or a change
                // to the CRT values.
                if field < 5 && !(change == 1 && field < 2) {
                    prop_assert_eq!(ours.is_ok(), oracle.is_ok(), "field {} change {}", field, change);
                }
                if let Ok(ours) = &ours {
                    let oracle = oracle.unwrap();
                    let (oracle_pkcs8, ours_pkcs8) = (oracle.to_pkcs8_der().unwrap(), ours.to_pkcs8());
                    prop_assert_eq!(oracle_pkcs8.as_bytes(), ours_pkcs8.as_ref());
                    let signature = ours.sign(&sign::PKCS1_SHA256, b"hello").unwrap();
                    prop_assert_eq!(
                        oracle.pkcs1v15_sign::<::sha2::Sha256>(b"hello").unwrap(),
                        signature.as_ref()
                    );
                }
                if let (Ok(ours), Ok(them)) = (ours, them) {
                    let (ours_pkcs8, them_pkcs8) = (ours.to_pkcs8(), them.as_der().unwrap());
                    prop_assert_eq!(ours_pkcs8.as_ref(), them_pkcs8.as_ref());
                    let signature = ours.sign(&sign::PSS_SHA256, b"hello").unwrap();
                    UnparsedPublicKey::new(&signature::RSA_PSS_2048_8192_SHA256, them.public_key())
                        .verify(b"hello", signature.as_ref())
                        .unwrap();
                }
            }
        }
    }

    /// aws-lc-rs and rind load an 8192-bit key whose private integers have
    /// more leading zero bytes than their slots leave room for, since its
    /// primes take every word, to the same PKCS#8.
    #[test]
    fn from_components_padded() {
        let pkcs8 = include_bytes!("../src/high/rsa/rsa8192.pkcs8.der");
        for pad in [2, 9] {
            let mut fields = components(pkcs8);
            for value in &mut fields[2..] {
                value.splice(0..0, vec![0; pad]);
            }
            let [n, e, d, p, q, dp, dq, qi] = &fields[..] else {
                unreachable!()
            };
            let ours = RsaKeyPair::from_components(&rind::rsa::KeyPairComponents {
                public_key: rind::rsa::PublicKeyComponents { n, e },
                d,
                p,
                q,
                dp,
                dq,
                qi,
            })
            .unwrap();
            let them = KeyPair::from_components(&aws_lc_rs::rsa::KeyPairComponents {
                public_key: aws_lc_rs::rsa::PublicKeyComponents { n, e },
                d,
                p,
                q,
                dP: dp,
                dQ: dq,
                qInv: qi,
            })
            .unwrap();
            assert_eq!(ours.to_pkcs8().as_ref(), them.as_der().unwrap().as_ref());
            assert_eq!(ours.to_pkcs8().as_ref(), &pkcs8[..]);
        }
    }

    /// The DER element starting `der`: its contents, and what follows it.
    fn element(der: &[u8]) -> (&[u8], &[u8]) {
        let (len, at) = match der[1] {
            0x81 => (usize::from(der[2]), 3),
            0x82 => (usize::from(u16::from_be_bytes([der[2], der[3]])), 4),
            len => (usize::from(len), 2),
        };
        (&der[at..at + len], &der[at + len..])
    }

    /// A PKCS#8 RSA key's integers in `RSAPrivateKey` order (n, e, d, p, q,
    /// dP, dQ, qInv), without DER's sign bytes.
    fn components(pkcs8: &[u8]) -> Vec<Vec<u8>> {
        let (pkcs8, _) = element(pkcs8);
        let (_version, rest) = element(pkcs8);
        let (_algorithm, rest) = element(rest);
        let (pkcs1, _) = element(rest);
        let (pkcs1, _) = element(pkcs1);
        let (_version, mut rest) = element(pkcs1);
        let mut out = Vec::new();
        while !rest.is_empty() {
            let (value, next) = element(rest);
            out.push(value.strip_prefix(&[0]).unwrap_or(value).to_vec());
            rest = next;
        }
        out
    }

    /// RustCrypto's verdict on a PKCS#1 v1.5 or PSS signature.
    type Oracle = fn(&::rsa::PublicKey, &[u8], &[u8]) -> bool;

    fn pkcs1<D: ::sha2::Digest + ::sha2::digest::const_oid::AssociatedOid>(
        key: &::rsa::PublicKey,
        message: &[u8],
        signature: &[u8],
    ) -> bool {
        key.pkcs1v15_verify::<D>(message, signature).is_ok()
    }

    fn pss<D: ::sha2::Digest + ::sha2::digest::FixedOutputReset>(
        key: &::rsa::PublicKey,
        message: &[u8],
        signature: &[u8],
    ) -> bool {
        key.pss_verify::<D>(message, signature).is_ok()
    }

    // Every verification algorithm, beside aws-lc-rs's of the same name, and
    // RustCrypto's with the smallest modulus, in bits, the algorithm takes,
    // which RustCrypto does not check.
    const VERIFICATION: [(
        &RsaVerificationAlgorithm,
        &signature::RsaParameters,
        usize,
        Oracle,
    ); 11] = [
        (
            &verify::legacy::PKCS1_1024_SHA1,
            &signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
            1024,
            pkcs1::<::sha1::Sha1>,
        ),
        (
            &verify::legacy::PKCS1_1024_SHA256,
            &signature::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
            1024,
            pkcs1::<::sha2::Sha256>,
        ),
        (
            &verify::legacy::PKCS1_1024_SHA512,
            &signature::RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
            1024,
            pkcs1::<::sha2::Sha512>,
        ),
        (
            &verify::legacy::PKCS1_SHA1,
            &signature::RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
            2048,
            pkcs1::<::sha1::Sha1>,
        ),
        (
            &verify::PKCS1_SHA256,
            &signature::RSA_PKCS1_2048_8192_SHA256,
            2048,
            pkcs1::<::sha2::Sha256>,
        ),
        (
            &verify::PKCS1_SHA384,
            &signature::RSA_PKCS1_2048_8192_SHA384,
            2048,
            pkcs1::<::sha2::Sha384>,
        ),
        (
            &verify::PKCS1_SHA512,
            &signature::RSA_PKCS1_2048_8192_SHA512,
            2048,
            pkcs1::<::sha2::Sha512>,
        ),
        (
            &verify::legacy::PKCS1_3072_SHA384,
            &signature::RSA_PKCS1_3072_8192_SHA384,
            3072,
            pkcs1::<::sha2::Sha384>,
        ),
        (
            &verify::PSS_SHA256,
            &signature::RSA_PSS_2048_8192_SHA256,
            2048,
            pss::<::sha2::Sha256>,
        ),
        (
            &verify::PSS_SHA384,
            &signature::RSA_PSS_2048_8192_SHA384,
            2048,
            pss::<::sha2::Sha384>,
        ),
        (
            &verify::PSS_SHA512,
            &signature::RSA_PSS_2048_8192_SHA512,
            2048,
            pss::<::sha2::Sha512>,
        ),
    ];

    /// All three accept and refuse the same signatures under every
    /// algorithm, for keys as DER or as components. aws-lc-rs signs neither
    /// SHA-1 nor 1024-bit keys, so the signatures are Wycheproof's.
    #[test]
    fn verification_agrees() {
        for file in [
            "rsa_pkcs1_1024_sig_gen_test.json",
            "rsa_pkcs1_2048_sig_gen_test.json",
        ] {
            let path = format!(
                "{}/../thirdparty/vectors/wycheproof/testvectors_v1/{file}",
                env!("CARGO_MANIFEST_DIR")
            );
            let tests: serde_json::Value =
                serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
            for group in tests["testGroups"].as_array().unwrap() {
                let hex = |value: &serde_json::Value| hex::decode(value.as_str().unwrap()).unwrap();
                let der = hex(&group["keyAsn"]);
                let modulus = hex(&group["privateKey"]["modulus"]);
                let e = hex(&group["privateKey"]["publicExponent"]);
                // A leading zero, as the DER sign byte leaves, is refused.
                let n = modulus.strip_prefix(&[0]).unwrap();
                let bits = n.len() * 8 - n[0].leading_zeros() as usize;
                let oracle = ::rsa::PublicKey::from_pkcs1_der(&der).unwrap();

                for (i, test) in group["tests"].as_array().unwrap().iter().enumerate() {
                    let message = hex(&test["msg"]);
                    let signature = hex(&test["sig"]);
                    let other = [&message[..], b"!"].concat();
                    // Another message is refused alike, so checking it once
                    // per group keeps this fast under emulation.
                    let messages = match i {
                        0 => &[&message[..], &other][..],
                        _ => &[&message[..]],
                    };

                    for message in messages {
                        for (ours, theirs, min_bits, oracle_verify) in VERIFICATION {
                            let case = format!("{file} {i} {ours:?}");
                            for n in [n, &modulus] {
                                let components = rind::rsa::PublicKeyComponents { n, e: &e };
                                let ours = rind::rsa::PublicKey::from_components(&components)
                                    .and_then(|key| key.verify(ours, message, &signature));
                                let theirs = signature::RsaPublicKeyComponents { n, e: &e }
                                    .verify(theirs, message, &signature);
                                assert_eq!(ours.is_ok(), theirs.is_ok(), "{case} {ours:?}");
                            }

                            let ours = rind::rsa::PublicKey::new(&der)
                                .and_then(|key| key.verify(ours, message, &signature));
                            let theirs =
                                UnparsedPublicKey::new(theirs, &der).verify(message, &signature);
                            assert_eq!(ours.is_ok(), theirs.is_ok(), "{case} {ours:?}");
                            let oracle =
                                bits >= min_bits && oracle_verify(&oracle, message, &signature);
                            assert_eq!(ours.is_ok(), oracle, "{case} {ours:?}, RustCrypto");
                        }
                    }
                }
            }
        }
    }

    /// aws-lc refuses a 2047-bit private key, which rind loads, as two
    /// 1024-bit primes give it the strength of 2048 bits and ring loads it;
    /// rind-aws-lc-rs refuses it as aws-lc-rs does.
    #[test]
    fn loads_2047_bit_private_key() {
        let private = include_bytes!("../src/high/rsa/rsa2047.pkcs8.der");
        assert!(KeyPair::from_pkcs8(private).is_err());
        let ours = RsaKeyPair::from_pkcs8(private).unwrap();
        // OpenSSL drew its primes at 1024 and 1023 bits, so ring refuses it.
        assert_eq!(ours.prime_bits(), [1024, 1023]);
        assert!(ours.sign(&sign::PKCS1_SHA256, b"message").is_ok());
        // One bit less, with two 1023-bit primes, both refuse.
        let too_small = include_bytes!("../src/high/rsa/rsa2046.der");
        assert!(aws_lc_rs::rsa::KeyPair::from_der(too_small).is_err());
        assert!(matches!(
            RsaKeyPair::from_pkcs1(too_small),
            Err(Error::KeyRejected(_))
        ));
        // The public key parses, as a legacy algorithm verifies with it,
        // and the others refuse it.
        let public = include_bytes!("../src/high/rsa/rsa2047.pub.der");
        let public = rind::rsa::PublicKey::new(public).unwrap();
        // So a caller can refuse it at load, as aws-lc-rs's length reads it.
        assert_eq!(public.modulus_len(), 256);
        assert!(matches!(
            public.verify(&verify::PKCS1_SHA256, b"message", &[0; 256]),
            Err(Error::KeyRejected(_))
        ));
    }

    /// An OpenSSL key with e = 2^33 + 1, just past the 33 bits both take, and
    /// its signature over "message", which OpenSSL verifies.
    #[test]
    fn refuses_exponent_over_33_bits() {
        let private = include_bytes!("../src/high/rsa/rsa2048-e34.pkcs8.der");
        assert!(KeyPair::from_pkcs8(private).is_err());
        assert!(matches!(
            RsaKeyPair::from_pkcs8(private),
            Err(Error::KeyRejected(_))
        ));
        let public = include_bytes!("../src/high/rsa/rsa2048-e34.pub.der");
        let signature = include_bytes!("../src/high/rsa/rsa2048-e34.sig");
        assert!(
            UnparsedPublicKey::new(&signature::RSA_PKCS1_2048_8192_SHA256, public)
                .verify(b"message", signature)
                .is_err()
        );
        assert!(matches!(
            rind::rsa::PublicKey::new(public),
            Err(Error::KeyRejected(_))
        ));
    }

    mod oaep {
        use ::rsa::pkcs8::DecodePrivateKey;
        use ::sha2::digest::{Digest, FixedOutputReset};
        use aws_lc_rs::encoding::{AsDer, PublicKeyX509Der};
        use aws_lc_rs::rand::SystemRandom;
        use aws_lc_rs::rsa::{
            OAEP_SHA1_MGF1SHA1, OAEP_SHA256_MGF1SHA256, OAEP_SHA384_MGF1SHA384,
            OAEP_SHA512_MGF1SHA512, OaepAlgorithm, OaepPrivateDecryptingKey,
            OaepPublicEncryptingKey, PrivateDecryptingKey, PublicEncryptingKey,
        };
        use aws_lc_rs::signature::{self, KeyPair as _, UnparsedPublicKey};
        use proptest::collection::vec;
        use proptest::prelude::*;
        use rind::Error;
        use rind::rsa::verify;
        use rind::rsa::{self as ours, DecryptingKey, EncryptingKey};

        use super::THEIRS;
        use crate::der;

        /// The object identifiers of `rsaEncryption`, `id-RSAES-OAEP`, and
        /// X.509's `id-ea-rsa`, all for the same key, and of RSASSA-PSS, which
        /// restricts it.
        const RSA_ENCRYPTION: [u8; 11] = [
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01,
        ];
        const RSAES_OAEP: [u8; 11] = [
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x07,
        ];
        const EA_RSA: [u8; 6] = [0x06, 0x04, 0x55, 0x08, 0x01, 0x01];
        const RSASSA_PSS: [u8; 11] = [
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a,
        ];

        const ALGORITHMS: [(&ours::OaepAlgorithm, &OaepAlgorithm, Oracle); 4] = [
            (
                &ours::legacy::OAEP_SHA1,
                &OAEP_SHA1_MGF1SHA1,
                Oracle::of::<::sha1::Sha1>(),
            ),
            (
                &ours::OAEP_SHA256,
                &OAEP_SHA256_MGF1SHA256,
                Oracle::of::<::sha2::Sha256>(),
            ),
            (
                &ours::OAEP_SHA384,
                &OAEP_SHA384_MGF1SHA384,
                Oracle::of::<::sha2::Sha384>(),
            ),
            (
                &ours::OAEP_SHA512,
                &OAEP_SHA512_MGF1SHA512,
                Oracle::of::<::sha2::Sha512>(),
            ),
        ];

        /// RustCrypto's OAEP with one hash, for both the label and MGF1, and
        /// its key.
        #[derive(Clone, Copy)]
        struct Oracle {
            encrypt: fn(&::rsa::PublicKey, &[u8], &[u8]) -> Vec<u8>,
            decrypt: fn(&::rsa::PrivateKey, &[u8], &[u8]) -> Decrypted,
        }

        /// The message, or `None` where the key refuses the ciphertext.
        type Decrypted = Option<Vec<u8>>;

        impl Oracle {
            const fn of<D: Digest + FixedOutputReset>() -> Self {
                Self {
                    encrypt: |key, message, label| {
                        let padding = ::rsa::Oaep::<D>::new_with_label(label);
                        key.encrypt(&mut getrandom::SysRng, padding, message)
                            .unwrap()
                    },
                    decrypt: |key, ciphertext, label| {
                        let padding = ::rsa::Oaep::<D>::new_with_label(label);
                        key.decrypt(padding, ciphertext).ok()
                    },
                }
            }
        }

        /// For each of `THEIRS` and each algorithm, loaded from its PKCS#8:
        /// our key, aws-lc-rs's and its public key, and RustCrypto's.
        fn keys() -> impl Iterator<
            Item = (
                &'static ours::OaepAlgorithm,
                &'static OaepAlgorithm,
                DecryptingKey,
                OaepPrivateDecryptingKey,
                PublicEncryptingKey,
                (Oracle, ::rsa::PrivateKey),
            ),
        > {
            THEIRS.iter().flat_map(|theirs| {
                let pkcs8 = theirs.as_der().unwrap();
                ALGORITHMS.map(|(ours_algorithm, theirs_algorithm, oracle)| {
                    let ours = DecryptingKey::from_pkcs8(ours_algorithm, pkcs8.as_ref()).unwrap();
                    let theirs = PrivateDecryptingKey::from_pkcs8(pkcs8.as_ref()).unwrap();
                    let public = theirs.public_key();
                    let oracle_key = ::rsa::PrivateKey::from_pkcs8_der(pkcs8.as_ref()).unwrap();
                    (
                        ours_algorithm,
                        theirs_algorithm,
                        ours,
                        OaepPrivateDecryptingKey::new(theirs).unwrap(),
                        public,
                        (oracle, oracle_key),
                    )
                })
            })
        }

        fn decrypt(
            key: &OaepPrivateDecryptingKey,
            algorithm: &'static OaepAlgorithm,
            ciphertext: &[u8],
            label: &[u8],
        ) -> Option<Vec<u8>> {
            let mut out = vec![0; key.min_output_size()];
            let out = key
                .decrypt(algorithm, ciphertext, &mut out, Some(label))
                .ok()?;
            Some(out.to_vec())
        }

        // Each case makes several private-key operations per key and
        // algorithm, which are slow under emulation.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(4))]

            /// Each decrypts what the other encrypts, through the SPKI each
            /// gives the other.
            #[test]
            fn encrypt_decrypt(
                message in vec(any::<u8>(), 0..200),
                label in vec(any::<u8>(), 0..40),
            ) {
                for (ours_algorithm, theirs_algorithm, ours, theirs, public, (oracle, oracle_key)) in
                    keys()
                {
                    let spki: PublicKeyX509Der<'_> = public.as_der().unwrap();
                    let ours_spki = ours.public_key().to_spki();
                    prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
                    let ours_public = EncryptingKey::from_spki(ours_algorithm, spki.as_ref()).unwrap();
                    let ours_public_spki = ours_public.to_spki();
                    prop_assert_eq!(ours_public_spki.as_ref(), spki.as_ref());
                    let theirs_public = OaepPublicEncryptingKey::new(
                        PublicEncryptingKey::from_der(ours_public_spki.as_ref()).unwrap(),
                    )
                    .unwrap();

                    let max = theirs_public.max_plaintext_size(theirs_algorithm);
                    prop_assert_eq!(ours_public.max_message_len(), max);
                    let message = &message[..message.len().min(max)];

                    let ciphertext = ours_public.encrypt(message, &label).unwrap();
                    let decrypted = decrypt(&theirs, theirs_algorithm, ciphertext.as_ref(), &label);
                    prop_assert_eq!(decrypted.as_deref(), Some(message));

                    let mut ciphertext = vec![0; theirs_public.ciphertext_size()];
                    let ciphertext = theirs_public
                        .encrypt(theirs_algorithm, message, &mut ciphertext, Some(&label))
                        .unwrap();
                    let decrypted = ours.decrypt(ciphertext, &label).unwrap();
                    prop_assert_eq!(decrypted.as_ref(), message);

                    // And with RustCrypto.
                    let ciphertext = ours_public.encrypt(message, &label).unwrap();
                    let decrypted = (oracle.decrypt)(&oracle_key, ciphertext.as_ref(), &label);
                    prop_assert_eq!(decrypted.as_deref(), Some(message));
                    let ciphertext = (oracle.encrypt)(oracle_key.as_public_key(), message, &label);
                    let decrypted = ours.decrypt(&ciphertext, &label).unwrap();
                    prop_assert_eq!(decrypted.as_ref(), message);
                }
            }

            /// All three accept the same ciphertexts, tampered with or made
            /// up, and decrypt them to the same message.
            #[test]
            fn decrypt_agrees(
                flip in any::<prop::sample::Index>(),
                bytes in vec(any::<u8>(), 256..=257),
            ) {
                for (_, theirs_algorithm, ours, theirs, _, (oracle, oracle_key)) in keys() {
                    let ciphertext = ours.public_key().encrypt(b"message", b"").unwrap();
                    let mut tampered = ciphertext.as_ref().to_vec();
                    let i = flip.index(tampered.len());
                    tampered[i] ^= 1;
                    for ciphertext in [&tampered, &bytes] {
                        let ours = ours.decrypt(ciphertext, b"");
                        let theirs = decrypt(&theirs, theirs_algorithm, ciphertext, b"");
                        let oracle = (oracle.decrypt)(&oracle_key, ciphertext, b"");
                        match (&ours, &theirs, &oracle) {
                            (Ok(ours), Some(theirs), Some(oracle)) => {
                                prop_assert_eq!(ours.as_ref(), &theirs[..]);
                                prop_assert_eq!(ours.as_ref(), &oracle[..]);
                            }
                            (Err(Error::DecryptFailed), None, None) => {}
                            _ => prop_assert!(
                                false,
                                "ours {:?}, theirs {:?}, RustCrypto {:?}",
                                ours,
                                theirs,
                                oracle
                            ),
                        }
                    }
                }
            }
        }

        /// RSA SPKI forms through `EncryptingKey::from_spki` and
        /// `rsa::PublicKey::from_spki`, each beside aws-lc-rs, which also
        /// ignores the algorithm's parameters and bytes after the SPKI.
        #[test]
        fn spki_forms_agree() {
            let theirs = &THEIRS[0];
            let pkcs1 = theirs.public_key().as_ref();
            let rsa_encryption = RSA_ENCRYPTION;
            let ec_public_key = [0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
            let null = |oid: &[u8]| [oid, &[0x05, 0x00]].concat();
            let rsa_null = null(&rsa_encryption);
            let spki = |algorithm: &[u8], bits: &[u8]| {
                der(0x30, &[der(0x30, algorithm), der(0x03, bits)].concat())
            };
            let key = [&[0][..], pkcs1].concat();

            // Each form, whether rind takes it, and whether aws-lc-rs does.
            let cases: [(&str, Vec<u8>, bool, bool); 14] = [
                ("canonical", spki(&rsa_null, &key), true, true),
                ("no parameters", spki(&rsa_encryption, &key), true, true),
                ("id-RSAES-OAEP", spki(&null(&RSAES_OAEP), &key), true, true),
                (
                    "id-RSAES-OAEP, no parameters",
                    spki(&RSAES_OAEP, &key),
                    true,
                    true,
                ),
                (
                    "id-RSAES-OAEP, default RSAES-OAEP-params",
                    spki(&[&RSAES_OAEP[..], &[0x30, 0x00]].concat(), &key),
                    false,
                    true,
                ),
                ("id-ea-rsa", spki(&null(&EA_RSA), &key), true, true),
                ("id-ea-rsa, no parameters", spki(&EA_RSA, &key), true, true),
                (
                    "empty-sequence parameters",
                    spki(&[&rsa_encryption[..], &[0x30, 0x00]].concat(), &key),
                    false,
                    true,
                ),
                ("RSASSA-PSS", spki(&null(&RSASSA_PSS), &key), false, false),
                ("EC", spki(&null(&ec_public_key), &key), false, false),
                (
                    "unused bits",
                    spki(&rsa_null, &[&[1][..], pkcs1].concat()),
                    false,
                    false,
                ),
                ("empty bit string", spki(&rsa_null, &[]), false, false),
                (
                    "trailing data",
                    [spki(&rsa_null, &key), vec![0]].concat(),
                    false,
                    true,
                ),
                (
                    "trailing key data",
                    spki(&rsa_null, &[&key[..], &[0]].concat()),
                    false,
                    false,
                ),
            ];
            assert_eq!(cases[0].1, theirs.public_key().as_der().unwrap().as_ref());

            let message = b"message";
            let mut signature = vec![0; theirs.public_modulus_len()];
            theirs
                .sign(
                    &signature::RSA_PKCS1_SHA256,
                    &SystemRandom::new(),
                    message,
                    &mut signature,
                )
                .unwrap();

            for (case, der, ours_take, theirs_take) in &cases {
                assert_eq!(
                    PublicEncryptingKey::from_der(der).is_ok(),
                    *theirs_take,
                    "{case}"
                );
                let ours = EncryptingKey::from_spki(&ours::OAEP_SHA256, der);
                assert_eq!(ours.is_ok(), *ours_take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.as_ref(), pkcs1, "{case}");
                }

                let theirs = UnparsedPublicKey::new(&signature::RSA_PKCS1_2048_8192_SHA256, der)
                    .verify(message, &signature);
                assert_eq!(theirs.is_ok(), *theirs_take, "{case}");
                let ours = ours::PublicKey::from_spki(der);
                assert_eq!(ours.is_ok(), *ours_take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.as_ref(), pkcs1, "{case}");
                    ours.verify(&verify::PKCS1_SHA256, message, &signature)
                        .unwrap();
                }
            }
        }

        /// RSA PKCS#8 algorithm identifiers through `DecryptingKey` and
        /// `rsa::KeyPair`, each beside aws-lc-rs, which requires `NULL`
        /// parameters for every RSA algorithm it takes.
        #[test]
        fn pkcs8_algorithms_agree() {
            let theirs = &THEIRS[0];
            let canonical = theirs.as_der().unwrap();
            let canonical = canonical.as_ref();
            let rsa_null = [
                0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05,
                0x00,
            ];
            let at = canonical
                .windows(rsa_null.len())
                .position(|w| w == rsa_null)
                .unwrap();
            let (version, private_key) = (&canonical[4..at], &canonical[at + rsa_null.len()..]);
            let pkcs8 = |algorithm: &[u8]| {
                der(
                    0x30,
                    &[version, &der(0x30, algorithm), private_key].concat(),
                )
            };
            let null = |oid: &[u8]| [oid, &[0x05, 0x00]].concat();

            // Each algorithm identifier, and whether both sides take it.
            let cases: [(&str, Vec<u8>, bool); 9] = [
                ("rsaEncryption", null(&RSA_ENCRYPTION), true),
                (
                    "rsaEncryption, no parameters",
                    RSA_ENCRYPTION.to_vec(),
                    false,
                ),
                ("id-RSAES-OAEP", null(&RSAES_OAEP), true),
                ("id-RSAES-OAEP, no parameters", RSAES_OAEP.to_vec(), false),
                (
                    "id-RSAES-OAEP, default RSAES-OAEP-params",
                    [&RSAES_OAEP[..], &[0x30, 0x00]].concat(),
                    false,
                ),
                ("id-ea-rsa", null(&EA_RSA), true),
                ("id-ea-rsa, no parameters", EA_RSA.to_vec(), false),
                (
                    "id-ea-rsa, KeySize",
                    [&EA_RSA[..], &[0x02, 0x02, 0x08, 0x00]].concat(),
                    false,
                ),
                ("RSASSA-PSS", null(&RSASSA_PSS), false),
            ];
            assert_eq!(pkcs8(&cases[0].1), canonical);

            let public = theirs.public_key().as_ref();
            for (case, algorithm, take) in &cases {
                let der = pkcs8(algorithm);
                let theirs = PrivateDecryptingKey::from_pkcs8(&der);
                assert_eq!(theirs.is_ok(), *take, "{case}");
                let theirs = aws_lc_rs::rsa::KeyPair::from_pkcs8(&der);
                assert_eq!(theirs.is_ok(), *take, "{case}");

                let ours = DecryptingKey::from_pkcs8(&ours::OAEP_SHA256, &der);
                assert_eq!(ours.is_ok(), *take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.public_key().as_ref(), public, "{case}");
                    // It writes back as `rsaEncryption`, as aws-lc does.
                    assert_eq!(ours.to_pkcs8().as_ref(), canonical, "{case}");
                }
                let ours = ours::KeyPair::from_pkcs8(&der);
                assert_eq!(ours.is_ok(), *take, "{case}: {ours:?}");
                if let Ok(ours) = ours {
                    assert_eq!(ours.public_key().as_ref(), public, "{case}");
                }
            }
        }
    }
}

/// Each side of RFC 9474's protocol against blind-rsa-signatures' other
/// side, for each variant.
mod blind_rsa {
    use blind_rsa_signatures::{
        DefaultRng, Deterministic, MessagePrepare, MessageRandomizer, PSS, PSSZero, Randomized,
        SaltMode, SecretKey, Sha384,
    };
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::blind_rsa::*;

    // Their keys are 2048 to 4096 bits.
    const KEYS: [&[u8]; 2] = [
        include_bytes!("../src/high/rsa/rsa2048.pkcs8.der"),
        include_bytes!("../src/high/rsa/rsa4096.pkcs8.der"),
    ];

    fn check<S: SaltMode, M: MessagePrepare>(algorithm: &'static Algorithm, message: &[u8]) {
        for der in KEYS {
            let ours = KeyPair::from_pkcs8(algorithm, der).unwrap();
            let theirs = SecretKey::<Sha384, S, M>::from_der(der).unwrap();
            let our_public = ours.public_key();
            let their_public = theirs.public_key().unwrap();
            let spki = their_public.to_spki().unwrap();
            assert_eq!(our_public.to_spki().as_ref(), spki);
            PublicKey::from_spki(algorithm, &spki).unwrap();

            // Our client, their server.
            let (blinded, blinding) = our_public.blind(message).unwrap();
            let blind_signature = theirs.blind_sign(blinded.as_ref()).unwrap();
            let signature = blinding.finalize(&blind_signature).unwrap();
            let (prefix, rsa_signature) = signature.as_ref().split_at(match M::RANDOMIZE {
                true => 32,
                false => 0,
            });
            let randomizer = M::RANDOMIZE.then(|| MessageRandomizer(prefix.try_into().unwrap()));
            their_public
                .verify(&rsa_signature.to_vec().into(), randomizer, message)
                .unwrap();

            // Their client, our server.
            let result = their_public.blind(&mut DefaultRng, message).unwrap();
            let blind_signature = ours.blind_sign(&result.blind_message).unwrap();
            let blind_signature = blind_signature.as_ref().to_vec().into();
            let signature = their_public
                .finalize(&blind_signature, &result, message)
                .unwrap();
            let prefix = result.msg_randomizer.as_ref().map_or(&[][..], |r| &r.0[..]);
            our_public
                .verify(message, &[prefix, &signature].concat())
                .unwrap();
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn matches_blind_rsa_signatures(message in vec(any::<u8>(), 0..300)) {
            check::<PSS, Randomized>(&RSABSSA_SHA384_PSS_RANDOMIZED, &message);
            check::<PSSZero, Randomized>(&RSABSSA_SHA384_PSSZERO_RANDOMIZED, &message);
            check::<PSS, Deterministic>(&RSABSSA_SHA384_PSS_DETERMINISTIC, &message);
            check::<PSSZero, Deterministic>(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, &message);
        }
    }
}
