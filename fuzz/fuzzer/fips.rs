#![no_main]

//! rind-fips's services, each on arbitrary lengths and malformed keys,
//! against the same call on rind, from whose source the module is built.
//! The module is a shared library behind a C ABI, so every call crosses it:
//! under cargo fuzz's `--cfg fuzzing`, rind-fips builds it with this
//! target's coverage and sanitizer flags, so libFuzzer sees inside it and
//! AddressSanitizer checks its heap. A call the module accepts must be one
//! rind accepts, giving the same bytes, and verdicts on signatures, tags,
//! and ciphertexts under keys both load match rind's outright. FIPS 140-3
//! refuses some inputs rind takes, such as a PBKDF2 salt under 16 bytes, so
//! elsewhere the module may refuse more.
//!
//! The module builds only for little-endian 64-bit glibc Linux on x86_64 and
//! aarch64; elsewhere this target does nothing.

use libfuzzer_sys::fuzz_target;

// Unused where the target does nothing.
#[allow(dead_code)]
mod edit;
mod fixtures;

#[cfg(all(
    target_os = "linux",
    target_env = "gnu",
    target_endian = "little",
    target_pointer_width = "64",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fuzz_target!(|ops: Vec<module::Op>| {
    for op in ops.iter().take(16) {
        module::run(op);
    }
});

#[cfg(not(all(
    target_os = "linux",
    target_env = "gnu",
    target_endian = "little",
    target_pointer_width = "64",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
fuzz_target!(|_data: &[u8]| {});

#[cfg(all(
    target_os = "linux",
    target_env = "gnu",
    target_endian = "little",
    target_pointer_width = "64",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
mod module {
    use std::num::NonZeroU32;
    use std::sync::LazyLock;

    use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary};
    use rind_fips as fips;

    use crate::fixtures::Material;

    /// Checks that the module accepts only what rind does, with the same
    /// bytes, returning both results.
    fn agree<A: AsRef<[u8]>, B: AsRef<[u8]>>(
        ours: Result<A, fips::Error>,
        theirs: Result<B, rind::Error>,
    ) -> (Option<A>, Option<B>) {
        match (ours, theirs) {
            (Ok(ours), Ok(theirs)) => {
                assert_eq!(ours.as_ref(), theirs.as_ref());
                (Some(ours), Some(theirs))
            }
            (Ok(_), Err(error)) => panic!("the module accepts what rind refuses: {error:?}"),
            (Err(_), theirs) => (None, theirs.ok()),
        }
    }

    /// Checks that a verdict is rind's.
    fn same_verdict(ours: Result<(), fips::Error>, theirs: Result<(), rind::Error>) {
        assert_eq!(ours.is_ok(), theirs.is_ok(), "{ours:?} {theirs:?}");
    }

    fn pick<T: ?Sized>(choices: &[&'static T], index: u8) -> &'static T {
        choices[usize::from(index) % choices.len()]
    }

    #[derive(Arbitrary, Debug)]
    pub enum Op {
        Digest {
            algorithm: u8,
            chunks: Vec<Vec<u8>>,
        },
        Hmac {
            algorithm: u8,
            key: Vec<u8>,
            chunks: Vec<Vec<u8>>,
            tag: Vec<u8>,
        },
        Hkdf {
            algorithm: u8,
            salt: Vec<u8>,
            secret: Vec<u8>,
            info: Vec<Vec<u8>>,
            len: u16,
            prk: bool,
        },
        Pbkdf2 {
            algorithm: u8,
            secret: Vec<u8>,
            rounds: u16,
            salt: Vec<u8>,
            len: u16,
            previous: Vec<u8>,
        },
        AeadOpen {
            algorithm: u8,
            key: Vec<u8>,
            nonce: [u8; 12],
            aad: Vec<u8>,
            in_out: Vec<u8>,
        },
        GcmOpen {
            algorithm: u8,
            key: Vec<u8>,
            tag_len: u8,
            iv: Vec<u8>,
            aad: Vec<u8>,
            in_out: Vec<u8>,
        },
        RandomizedSeal {
            algorithm: u8,
            key: Vec<u8>,
            aad: Vec<u8>,
            plaintext: Vec<u8>,
            nonce: [u8; 12],
            open: Vec<u8>,
        },
        TlsSeal {
            algorithm: u8,
            key: Vec<u8>,
            records: Vec<(u64, Vec<u8>, Vec<u8>)>,
        },
        Quic {
            algorithm: u8,
            key: Vec<u8>,
            sample: [u8; 16],
        },
        Block {
            algorithm: u8,
            key: Vec<u8>,
            block: [u8; 16],
        },
        Ctr {
            algorithm: u8,
            key: Vec<u8>,
            bits: u8,
            counter: [u8; 16],
            in_out: Vec<u8>,
        },
        CbcEncrypt {
            algorithm: u8,
            key: Vec<u8>,
            iv: [u8; 16],
            pad: bool,
            in_out: Vec<u8>,
        },
        CbcDecrypt {
            algorithm: u8,
            key: Vec<u8>,
            iv: [u8; 16],
            pad: bool,
            in_out: Vec<u8>,
        },
        KeyWrap {
            algorithm: u8,
            kek: Vec<u8>,
            padded: bool,
            key: Vec<u8>,
            extra: u8,
        },
        KeyUnwrap {
            algorithm: u8,
            kek: Vec<u8>,
            padded: bool,
            wrapped: Vec<u8>,
            short: u8,
        },
        EcdsaPair {
            algorithm: u8,
            form: u8,
            bytes: Material,
            public_key: Vec<u8>,
            message: Vec<u8>,
        },
        EcdsaVerify {
            algorithm: u8,
            spki: bool,
            key: Material,
            message: Vec<u8>,
            signature: Vec<u8>,
        },
        Ed25519Pair {
            form: u8,
            bytes: Material,
            public_key: Vec<u8>,
            message: Vec<u8>,
        },
        Ed25519Verify {
            spki: bool,
            key: Material,
            message: Vec<u8>,
            signature: Vec<u8>,
        },
        MlDsaPair {
            set: u8,
            seed: Vec<u8>,
            message: Vec<u8>,
        },
        MlDsaVerify {
            set: u8,
            spki: bool,
            key: Vec<u8>,
            message: Vec<u8>,
            signature: Vec<u8>,
        },
        RsaPair {
            pkcs1: bool,
            bytes: Material,
            algorithm: u8,
            message: Vec<u8>,
        },
        RsaVerify {
            form: u8,
            key: Material,
            exponent: Vec<u8>,
            algorithm: u8,
            message: Vec<u8>,
            signature: Vec<u8>,
        },
        AgreementKey {
            algorithm: u8,
            form: u8,
            bytes: Material,
            peer: Vec<u8>,
        },
        AgreementPublic {
            algorithm: u8,
            spki: bool,
            bytes: Material,
        },
        Encapsulate {
            set: u8,
            key: Vec<u8>,
        },
        Decapsulate {
            ciphertext: Vec<u8>,
        },
        ConstantTime {
            a: Vec<u8>,
            b: Vec<u8>,
        },
        Rand {
            len: u16,
        },
    }

    pub fn run(op: &Op) {
        match op {
            Op::Digest { algorithm, chunks } => {
                let i = *algorithm;
                let (ours, theirs) = (
                    pick(
                        &[
                            &fips::digest::SHA256,
                            &fips::digest::SHA384,
                            &fips::digest::SHA512,
                            &fips::digest::SHA512_256,
                            &fips::digest::SHA3_256,
                            &fips::digest::SHA3_384,
                            &fips::digest::SHA3_512,
                        ],
                        i,
                    ),
                    pick(
                        &[
                            &rind::digest::SHA256,
                            &rind::digest::SHA384,
                            &rind::digest::SHA512,
                            &rind::digest::SHA512_256,
                            &rind::digest::SHA3_256,
                            &rind::digest::SHA3_384,
                            &rind::digest::SHA3_512,
                        ],
                        i,
                    ),
                );
                let mut context = fips::digest::Context::new(ours);
                let mut twin = rind::digest::Context::new(theirs);
                for chunk in chunks {
                    context.update(chunk);
                    twin.update(chunk);
                }
                assert_eq!(context.finish().as_ref(), twin.finish().as_ref());
                let whole = chunks.concat();
                assert_eq!(
                    fips::digest::digest(ours, &whole).as_ref(),
                    rind::digest::digest(theirs, &whole).as_ref()
                );
            }
            Op::Hmac {
                algorithm,
                key,
                chunks,
                tag,
            } => {
                let i = *algorithm;
                let ours = fips::hmac::Key::new(
                    pick(
                        &[
                            &fips::hmac::HMAC_SHA256,
                            &fips::hmac::HMAC_SHA384,
                            &fips::hmac::HMAC_SHA512,
                            &fips::hmac::legacy::HMAC_SHA1,
                        ],
                        i,
                    ),
                    key,
                );
                let theirs = rind::hmac::Key::new(
                    pick(
                        &[
                            &rind::hmac::HMAC_SHA256,
                            &rind::hmac::HMAC_SHA384,
                            &rind::hmac::HMAC_SHA512,
                            &rind::hmac::legacy::HMAC_SHA1,
                        ],
                        i,
                    ),
                    key,
                );
                let mut context = fips::hmac::Context::with_key(&ours);
                let mut twin = rind::hmac::Context::with_key(&theirs);
                for chunk in chunks {
                    context.update(chunk);
                    twin.update(chunk);
                }
                assert_eq!(context.sign().as_ref(), twin.sign().as_ref());
                let whole = chunks.concat();
                assert_eq!(
                    fips::hmac::sign(&ours, &whole).as_ref(),
                    rind::hmac::sign(&theirs, &whole).as_ref()
                );
                same_verdict(
                    fips::hmac::verify(&ours, &whole, tag),
                    rind::hmac::verify(&theirs, &whole, tag),
                );
            }
            Op::Hkdf {
                algorithm,
                salt,
                secret,
                info,
                len,
                prk,
            } => {
                let i = *algorithm;
                let ours_algorithm = pick(
                    &[
                        &fips::hkdf::HKDF_SHA256,
                        &fips::hkdf::HKDF_SHA384,
                        &fips::hkdf::HKDF_SHA512,
                        &fips::hkdf::legacy::HKDF_SHA1,
                    ],
                    i,
                );
                let theirs_algorithm = pick(
                    &[
                        &rind::hkdf::HKDF_SHA256,
                        &rind::hkdf::HKDF_SHA384,
                        &rind::hkdf::HKDF_SHA512,
                        &rind::hkdf::legacy::HKDF_SHA1,
                    ],
                    i,
                );
                let (ours, theirs) = if *prk {
                    (
                        Ok(fips::hkdf::Prk::new(ours_algorithm, secret)),
                        Ok(rind::hkdf::Prk::new(theirs_algorithm, secret)),
                    )
                } else {
                    (
                        fips::hkdf::Salt::new(ours_algorithm, salt).extract(secret),
                        rind::hkdf::Salt::new(theirs_algorithm, salt).extract(secret),
                    )
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();
                let (mut a, mut b) = (vec![0; usize::from(*len)], vec![0; usize::from(*len)]);
                let ours = ours.fill(&info, &mut a).map(|()| a);
                let theirs = theirs.fill(&info, &mut b).map(|()| b);
                agree(ours, theirs);
            }
            Op::Pbkdf2 {
                algorithm,
                secret,
                rounds,
                salt,
                len,
                previous,
            } => {
                let i = *algorithm;
                // Either side of the module's floor of 1000, and no more
                // than a fuzz iteration can afford.
                let Some(rounds) = NonZeroU32::new(u32::from(*rounds % 1100)) else {
                    return;
                };
                let ours = fips::pbkdf2::Secret::new(
                    pick(
                        &[
                            &fips::pbkdf2::PBKDF2_HMAC_SHA256,
                            &fips::pbkdf2::PBKDF2_HMAC_SHA384,
                            &fips::pbkdf2::PBKDF2_HMAC_SHA512,
                            &fips::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
                        ],
                        i,
                    ),
                    secret,
                );
                let theirs = rind::pbkdf2::Secret::new(
                    pick(
                        &[
                            &rind::pbkdf2::PBKDF2_HMAC_SHA256,
                            &rind::pbkdf2::PBKDF2_HMAC_SHA384,
                            &rind::pbkdf2::PBKDF2_HMAC_SHA512,
                            &rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
                        ],
                        i,
                    ),
                    secret,
                );
                // Each output block costs every round again.
                let len = usize::from(*len % 256);
                let (mut a, mut b) = (vec![0; len], vec![0; len]);
                let derived = ours.derive(rounds, salt, &mut a).map(|()| a);
                let twin = theirs.derive(rounds, salt, &mut b).map(|()| b);
                // The module takes exactly what rind takes within SP 800-132's
                // floors.
                let approved =
                    secret.len() >= 14 && salt.len() >= 16 && rounds.get() >= 1000 && len >= 14;
                assert_eq!(
                    derived.is_ok(),
                    twin.is_ok() && approved,
                    "{derived:?} {twin:?}"
                );
                // Verification refuses a key shorter than the hash's output.
                let hash_len = [32, 48, 64, 20][usize::from(i) % 4];
                if let (Some(derived), _) = agree(derived, twin) {
                    if derived.len() >= hash_len {
                        ours.verify(rounds, salt, &derived).unwrap();
                    }
                }
                let previous = &previous[..previous.len().min(256)];
                if ours.verify(rounds, salt, previous).is_ok() {
                    theirs.verify(rounds, salt, previous).unwrap();
                }
            }
            Op::AeadOpen {
                algorithm,
                key,
                nonce,
                aad,
                in_out,
            } => {
                let i = *algorithm;
                let ours = fips::aead::Key::new(
                    pick(
                        &[
                            &fips::aead::AES_128_GCM,
                            &fips::aead::AES_192_GCM,
                            &fips::aead::AES_256_GCM,
                        ],
                        i,
                    ),
                    key,
                );
                let theirs = rind::aead::Key::new(
                    pick(
                        &[
                            &rind::aead::AES_128_GCM,
                            &rind::aead::AES_192_GCM,
                            &rind::aead::AES_256_GCM,
                        ],
                        i,
                    ),
                    key,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let (mut a, mut b) = (in_out.clone(), in_out.clone());
                let opened = ours.open_in_place(
                    fips::aead::Nonce::assume_unique_for_key(*nonce),
                    aad,
                    &mut a,
                );
                let twin = theirs.open_in_place(
                    rind::aead::Nonce::assume_unique_for_key(*nonce),
                    aad,
                    &mut b,
                );
                same_verdict(
                    opened.as_ref().map(drop).map_err(|&e| e),
                    twin.as_ref().map(drop).map_err(|&e| e),
                );
                agree(opened, twin);
            }
            Op::GcmOpen {
                algorithm,
                key,
                tag_len,
                iv,
                aad,
                in_out,
            } => {
                use fips::aead::gcm::TagLength as Ours;
                use rind::aead::gcm::TagLength as Theirs;
                let i = *algorithm;
                let t = usize::from(*tag_len) % 7;
                let ours_tag = [
                    Ours::Full,
                    Ours::Truncated120,
                    Ours::Truncated112,
                    Ours::Truncated104,
                    Ours::Truncated96,
                    Ours::Truncated64,
                    Ours::Truncated32,
                ][t];
                let theirs_tag = [
                    Theirs::Full,
                    Theirs::Truncated120,
                    Theirs::Truncated112,
                    Theirs::Truncated104,
                    Theirs::Truncated96,
                    Theirs::Truncated64,
                    Theirs::Truncated32,
                ][t];
                let ours = fips::aead::gcm::Key::new(
                    pick(
                        &[
                            &fips::cipher::AES_128,
                            &fips::cipher::AES_192,
                            &fips::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                    ours_tag,
                );
                let theirs = rind::aead::gcm::Key::new(
                    pick(
                        &[
                            &rind::cipher::AES_128,
                            &rind::cipher::AES_192,
                            &rind::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                    theirs_tag,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let (ours_iv, theirs_iv) = (
                    fips::aead::gcm::Iv::assume_unique_for_key(iv),
                    rind::aead::gcm::Iv::assume_unique_for_key(iv),
                );
                let (Ok(ours_iv), Ok(theirs_iv)) = (ours_iv, theirs_iv) else {
                    assert!(fips::aead::gcm::Iv::assume_unique_for_key(iv).is_err());
                    return;
                };
                let (mut a, mut b) = (in_out.clone(), in_out.clone());
                let opened = ours.open_in_place(ours_iv, aad, &mut a);
                let twin = theirs.open_in_place(theirs_iv, aad, &mut b);
                same_verdict(
                    opened.as_ref().map(drop).map_err(|&e| e),
                    twin.as_ref().map(drop).map_err(|&e| e),
                );
                agree(opened, twin);
            }
            Op::RandomizedSeal {
                algorithm,
                key,
                aad,
                plaintext,
                nonce,
                open,
            } => {
                let i = *algorithm;
                let Ok(ours) = fips::aead::RandomizedNonceKey::new(
                    pick(
                        &[
                            &fips::aead::AES_128_GCM,
                            &fips::aead::AES_192_GCM,
                            &fips::aead::AES_256_GCM,
                        ],
                        i,
                    ),
                    key,
                ) else {
                    return;
                };
                let theirs = rind::aead::Key::new(
                    pick(
                        &[
                            &rind::aead::AES_128_GCM,
                            &rind::aead::AES_192_GCM,
                            &rind::aead::AES_256_GCM,
                        ],
                        i,
                    ),
                    key,
                )
                .unwrap();
                // The nonce is random: rind opens what the module sealed.
                let mut sealed = plaintext.clone();
                let nonce_used = ours.seal_in_place_append_tag(aad, &mut sealed).unwrap();
                let nonce_bytes: [u8; 12] = nonce_used.as_ref().try_into().unwrap();
                let opened = theirs
                    .open_in_place(
                        rind::aead::Nonce::assume_unique_for_key(nonce_bytes),
                        aad,
                        &mut sealed.clone(),
                    )
                    .unwrap()
                    .to_vec();
                assert_eq!(&opened, plaintext);
                // And the module opens arbitrary input as rind does.
                let (mut a, mut b) = (open.clone(), open.clone());
                let opened = ours.open_in_place(fips::aead::RandomNonce::from(*nonce), aad, &mut a);
                let twin = theirs.open_in_place(
                    rind::aead::Nonce::assume_unique_for_key(*nonce),
                    aad,
                    &mut b,
                );
                same_verdict(
                    opened.as_ref().map(drop).map_err(|&e| e),
                    twin.as_ref().map(drop).map_err(|&e| e),
                );
                agree(opened, twin);
            }
            Op::TlsSeal {
                algorithm,
                key,
                records,
            } => {
                // TLS takes AES-128-GCM and AES-256-GCM.
                let i = *algorithm;
                let Ok(mut ours) = fips::aead::TlsRecordSealingKey::new(
                    pick(&[&fips::aead::AES_128_GCM, &fips::aead::AES_256_GCM], i),
                    fips::aead::TlsProtocolId::TLS13,
                    key,
                ) else {
                    return;
                };
                let theirs = rind::aead::Key::new(
                    pick(&[&rind::aead::AES_128_GCM, &rind::aead::AES_256_GCM], i),
                    key,
                )
                .unwrap();
                // The key refuses a sequence number, the nonce XORed with the
                // first, not above the last, or one that would wrap; what it
                // seals is plain AES-GCM.
                let (mut first, mut next) = (None, 0);
                for (sequence, aad, plaintext) in records.iter().take(8) {
                    let mut nonce = [0; 12];
                    nonce[4..].copy_from_slice(&sequence.to_be_bytes());
                    let (mut a, mut b) = (plaintext.clone(), plaintext.clone());
                    let sealed = ours.seal_in_place_separate_tag(
                        fips::aead::Nonce::assume_unique_for_key(nonce),
                        aad,
                        &mut a,
                    );
                    let seq = sequence ^ *first.get_or_insert(*sequence);
                    if seq == u64::MAX || seq < next {
                        assert_eq!(sealed.err(), Some(fips::Error::MessageLimitReached));
                        continue;
                    }
                    next = seq + 1;
                    let tag = sealed.unwrap();
                    let twin = theirs
                        .seal_in_place_separate_tag(
                            rind::aead::Nonce::assume_unique_for_key(nonce),
                            aad,
                            &mut b,
                        )
                        .unwrap();
                    assert_eq!(a, b);
                    assert_eq!(tag.as_ref(), twin.as_ref());
                }
            }
            Op::Quic {
                algorithm,
                key,
                sample,
            } => {
                let i = *algorithm;
                let ours = fips::aead::quic::HeaderProtectionKey::new(
                    pick(&[&fips::aead::quic::AES_128, &fips::aead::quic::AES_256], i),
                    key,
                );
                let theirs = rind::aead::quic::HeaderProtectionKey::new(
                    pick(&[&rind::aead::quic::AES_128, &rind::aead::quic::AES_256], i),
                    key,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.mask(sample), theirs.mask(sample));
            }
            Op::Block {
                algorithm,
                key,
                block,
            } => {
                let i = *algorithm;
                let ours = fips::cipher::Aes::new(
                    pick(
                        &[
                            &fips::cipher::AES_128,
                            &fips::cipher::AES_192,
                            &fips::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                );
                let theirs = rind::cipher::Aes::new(
                    pick(
                        &[
                            &rind::cipher::AES_128,
                            &rind::cipher::AES_192,
                            &rind::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let (mut a, mut b) = (*block, *block);
                ours.encrypt_block(&mut a);
                theirs.encrypt_block(&mut b);
                assert_eq!(a, b);
            }
            Op::Ctr {
                algorithm,
                key,
                bits,
                counter,
                in_out,
            } => {
                let i = *algorithm;
                let ours = fips::cipher::AesCtr::new(
                    pick(
                        &[
                            &fips::cipher::AES_128,
                            &fips::cipher::AES_192,
                            &fips::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                    *bits,
                );
                let theirs = rind::cipher::AesCtr::new(
                    pick(
                        &[
                            &rind::cipher::AES_128,
                            &rind::cipher::AES_192,
                            &rind::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                    *bits,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let (mut a, mut b) = (in_out.clone(), in_out.clone());
                agree(
                    ours.apply_keystream(counter, &mut a).map(|()| a),
                    theirs.apply_keystream(counter, &mut b).map(|()| b),
                );
            }
            Op::CbcEncrypt {
                algorithm,
                key,
                iv,
                pad,
                in_out,
            } => {
                let i = *algorithm;
                let ours = fips::cipher::AesCbcEncryptingKey::new(
                    pick(
                        &[
                            &fips::cipher::AES_128,
                            &fips::cipher::AES_192,
                            &fips::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                );
                let theirs = rind::cipher::AesCbcEncryptingKey::new(
                    pick(
                        &[
                            &rind::cipher::AES_128,
                            &rind::cipher::AES_192,
                            &rind::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let (ours_iv, theirs_iv) = (
                    fips::cipher::CbcIv::assume_unpredictable(*iv),
                    rind::cipher::CbcIv::assume_unpredictable(*iv),
                );
                let (mut a, mut b) = (in_out.clone(), in_out.clone());
                if *pad {
                    agree(
                        ours.encrypt(ours_iv, &mut a).map(|()| a),
                        theirs.encrypt(theirs_iv, &mut b).map(|()| b),
                    );
                } else {
                    agree(
                        ours.encrypt_blocks(ours_iv, &mut a).map(|()| a),
                        theirs.encrypt_blocks(theirs_iv, &mut b).map(|()| b),
                    );
                }
            }
            Op::CbcDecrypt {
                algorithm,
                key,
                iv,
                pad,
                in_out,
            } => {
                let i = *algorithm;
                let ours = fips::cipher::AesCbcDecryptingKey::new(
                    pick(
                        &[
                            &fips::cipher::AES_128,
                            &fips::cipher::AES_192,
                            &fips::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                );
                let theirs = rind::cipher::AesCbcDecryptingKey::new(
                    pick(
                        &[
                            &rind::cipher::AES_128,
                            &rind::cipher::AES_192,
                            &rind::cipher::AES_256,
                        ],
                        i,
                    ),
                    key,
                );
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let (mut a, mut b) = (in_out.clone(), in_out.clone());
                if *pad {
                    let opened = ours.decrypt(iv, &mut a);
                    let twin = theirs.decrypt(iv, &mut b);
                    same_verdict(
                        opened.as_ref().map(drop).map_err(|&e| e),
                        twin.as_ref().map(drop).map_err(|&e| e),
                    );
                    agree(opened, twin);
                } else {
                    let opened = ours.decrypt_blocks(iv, &mut a);
                    let twin = theirs.decrypt_blocks(iv, &mut b);
                    same_verdict(opened, twin);
                    agree(opened.map(|()| a), twin.map(|()| b));
                }
            }
            Op::KeyWrap {
                algorithm,
                kek,
                padded,
                key,
                extra,
            } => {
                let (ours, theirs) = keks(*algorithm, kek);
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let modes = if *padded {
                    (fips::key_wrap::Mode::Kwp, rind::key_wrap::Mode::Kwp)
                } else {
                    (fips::key_wrap::Mode::Kw, rind::key_wrap::Mode::Kw)
                };
                // The wrapped length, give or take, so both refuse a wrong one.
                let len = (key.len() + 15) / 8 * 8 + usize::from(*extra % 4) * 8 - 8;
                let (mut a, mut b) = (vec![0; len], vec![0; len]);
                agree(
                    ours.wrap_key(modes.0, key, &mut a).map(|()| a),
                    theirs.wrap_key(modes.1, key, &mut b).map(|()| b),
                );
            }
            Op::KeyUnwrap {
                algorithm,
                kek,
                padded,
                wrapped,
                short,
            } => {
                let (ours, theirs) = keks(*algorithm, kek);
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                let modes = if *padded {
                    (fips::key_wrap::Mode::Kwp, rind::key_wrap::Mode::Kwp)
                } else {
                    (fips::key_wrap::Mode::Kw, rind::key_wrap::Mode::Kw)
                };
                let len = wrapped.len().saturating_sub(8 + usize::from(*short % 2));
                let (mut a, mut b) = (vec![0; len], vec![0; len]);
                let opened = ours.unwrap_key(modes.0, wrapped, &mut a);
                let twin = theirs.unwrap_key(modes.1, wrapped, &mut b);
                same_verdict(
                    opened.as_ref().map(drop).map_err(|&e| e),
                    twin.as_ref().map(drop).map_err(|&e| e),
                );
                agree(opened, twin);
            }
            Op::EcdsaPair {
                algorithm,
                form,
                bytes,
                public_key,
                message,
            } => {
                use fips::ecdsa::{KeyPair as Ours, sign as ours_sign};
                use rind::ecdsa::{KeyPair as Theirs, sign as theirs_sign};
                let i = *algorithm;
                let a = pick(
                    &[
                        &ours_sign::P256_SHA256_ASN1,
                        &ours_sign::P256_SHA256_FIXED,
                        &ours_sign::P384_SHA384_ASN1,
                        &ours_sign::P384_SHA384_FIXED,
                        &ours_sign::P521_SHA512_ASN1,
                        &ours_sign::P521_SHA512_FIXED,
                    ],
                    i,
                );
                let b = pick(
                    &[
                        &theirs_sign::P256_SHA256_ASN1,
                        &theirs_sign::P256_SHA256_FIXED,
                        &theirs_sign::P384_SHA384_ASN1,
                        &theirs_sign::P384_SHA384_FIXED,
                        &theirs_sign::P521_SHA512_ASN1,
                        &theirs_sign::P521_SHA512_FIXED,
                    ],
                    i,
                );
                let bytes = bytes.bytes();
                let (ours, theirs) = match form % 3 {
                    0 => (Ours::from_pkcs8(a, &bytes), Theirs::from_pkcs8(b, &bytes)),
                    1 => (Ours::from_sec1(a, &bytes), Theirs::from_sec1(b, &bytes)),
                    _ => (
                        Ours::from_scalar_and_public_key(a, &bytes, public_key),
                        Theirs::from_scalar_and_public_key(b, &bytes, public_key),
                    ),
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.to_pkcs8().as_ref(), theirs.to_pkcs8().as_ref());
                assert_eq!(ours.to_sec1().as_ref(), theirs.to_sec1().as_ref());
                assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
                assert_eq!(
                    ours.public_key().to_spki().as_ref(),
                    theirs.public_key().to_spki().as_ref()
                );
                // Signatures are randomized: rind verifies the module's.
                let signature = ours.sign(message).unwrap();
                theirs
                    .public_key()
                    .verify(message, signature.as_ref())
                    .unwrap();
            }
            Op::EcdsaVerify {
                algorithm,
                spki,
                key,
                message,
                signature,
            } => {
                use fips::ecdsa::{PublicKey as Ours, verify as o};
                use rind::ecdsa::{PublicKey as Theirs, verify as t};
                let i = *algorithm;
                let a = pick(
                    &[
                        &o::P256_SHA256_ASN1,
                        &o::P256_SHA384_ASN1,
                        &o::P256_SHA512_ASN1,
                        &o::P384_SHA256_ASN1,
                        &o::P384_SHA384_ASN1,
                        &o::P384_SHA512_ASN1,
                        &o::P521_SHA256_ASN1,
                        &o::P521_SHA384_ASN1,
                        &o::P521_SHA512_ASN1,
                        &o::P256_SHA256_FIXED,
                        &o::P384_SHA384_FIXED,
                        &o::P521_SHA512_FIXED,
                    ],
                    i,
                );
                let b = pick(
                    &[
                        &t::P256_SHA256_ASN1,
                        &t::P256_SHA384_ASN1,
                        &t::P256_SHA512_ASN1,
                        &t::P384_SHA256_ASN1,
                        &t::P384_SHA384_ASN1,
                        &t::P384_SHA512_ASN1,
                        &t::P521_SHA256_ASN1,
                        &t::P521_SHA384_ASN1,
                        &t::P521_SHA512_ASN1,
                        &t::P256_SHA256_FIXED,
                        &t::P384_SHA384_FIXED,
                        &t::P521_SHA512_FIXED,
                    ],
                    i,
                );
                let key = key.bytes();
                let (ours, theirs) = if *spki {
                    (Ours::from_spki(a, &key), Theirs::from_spki(b, &key))
                } else {
                    (Ours::new(a, &key), Theirs::new(b, &key))
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.as_ref(), theirs.as_ref());
                same_verdict(
                    ours.verify(message, signature),
                    theirs.verify(message, signature),
                );
            }
            Op::Ed25519Pair {
                form,
                bytes,
                public_key,
                message,
            } => {
                use fips::ed25519::KeyPair as Ours;
                use rind::ed25519::KeyPair as Theirs;
                let bytes = bytes.bytes();
                let (ours, theirs) = match form % 3 {
                    0 => (Ours::from_pkcs8(&bytes), Theirs::from_pkcs8(&bytes)),
                    1 => (Ours::from_seed(&bytes), Theirs::from_seed(&bytes)),
                    _ => (
                        Ours::from_seed_and_public_key(&bytes, public_key),
                        Theirs::from_seed_and_public_key(&bytes, public_key),
                    ),
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.to_pkcs8().as_ref(), theirs.to_pkcs8().as_ref());
                assert_eq!(ours.to_pkcs8v1().as_ref(), theirs.to_pkcs8v1().as_ref());
                assert_eq!(ours.to_seed().as_ref(), theirs.to_seed().as_ref());
                assert_eq!(ours.sign(message).as_ref(), theirs.sign(message).as_ref());
            }
            Op::Ed25519Verify {
                spki,
                key,
                message,
                signature,
            } => {
                use fips::ed25519::PublicKey as Ours;
                use rind::ed25519::PublicKey as Theirs;
                let key = key.bytes();
                let (ours, theirs) = if *spki {
                    (Ours::from_spki(&key), Theirs::from_spki(&key))
                } else {
                    (Ours::new(&key), Theirs::new(&key))
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                same_verdict(
                    ours.verify(message, signature),
                    theirs.verify(message, signature),
                );
            }
            Op::MlDsaPair { set, seed, message } => match set % 3 {
                0 => ml_dsa_pair::<fips::ml_dsa::MlDsa44, rind::ml_dsa::MlDsa44>(seed, message),
                1 => ml_dsa_pair::<fips::ml_dsa::MlDsa65, rind::ml_dsa::MlDsa65>(seed, message),
                _ => ml_dsa_pair::<fips::ml_dsa::MlDsa87, rind::ml_dsa::MlDsa87>(seed, message),
            },
            Op::MlDsaVerify {
                set,
                spki,
                key,
                message,
                signature,
            } => match set % 3 {
                0 => ml_dsa_verify::<fips::ml_dsa::MlDsa44, rind::ml_dsa::MlDsa44>(
                    *spki, key, message, signature,
                ),
                1 => ml_dsa_verify::<fips::ml_dsa::MlDsa65, rind::ml_dsa::MlDsa65>(
                    *spki, key, message, signature,
                ),
                _ => ml_dsa_verify::<fips::ml_dsa::MlDsa87, rind::ml_dsa::MlDsa87>(
                    *spki, key, message, signature,
                ),
            },
            Op::RsaPair {
                pkcs1,
                bytes,
                algorithm,
                message,
            } => {
                use fips::rsa::{KeyPair as Ours, sign as o};
                use rind::rsa::{KeyPair as Theirs, sign as t};
                let bytes = bytes.bytes();
                let (ours, theirs) = if *pkcs1 {
                    (Ours::from_pkcs1(&bytes), Theirs::from_pkcs1(&bytes))
                } else {
                    (Ours::from_pkcs8(&bytes), Theirs::from_pkcs8(&bytes))
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.to_pkcs8().as_ref(), theirs.to_pkcs8().as_ref());
                let i = *algorithm % 6;
                let a = pick(
                    &[
                        &o::PKCS1_SHA256,
                        &o::PKCS1_SHA384,
                        &o::PKCS1_SHA512,
                        &o::PSS_SHA256,
                        &o::PSS_SHA384,
                        &o::PSS_SHA512,
                    ],
                    i,
                );
                let b = pick(
                    &[
                        &t::PKCS1_SHA256,
                        &t::PKCS1_SHA384,
                        &t::PKCS1_SHA512,
                        &t::PSS_SHA256,
                        &t::PSS_SHA384,
                        &t::PSS_SHA512,
                    ],
                    i,
                );
                let Ok(signature) = ours.sign(a, message) else {
                    return;
                };
                let twin = theirs.sign(b, message).unwrap();
                if i < 3 {
                    // PKCS#1 v1.5 is deterministic.
                    assert_eq!(signature.as_ref(), twin.as_ref());
                } else {
                    let v = [
                        &rind::rsa::verify::PSS_SHA256,
                        &rind::rsa::verify::PSS_SHA384,
                        &rind::rsa::verify::PSS_SHA512,
                    ][usize::from(i - 3)];
                    theirs
                        .public_key()
                        .verify(v, message, signature.as_ref())
                        .unwrap();
                }
            }
            Op::RsaVerify {
                form,
                key,
                exponent,
                algorithm,
                message,
                signature,
            } => {
                use fips::rsa::{PublicKey as Ours, verify as o};
                use rind::rsa::{PublicKey as Theirs, verify as t};
                let key = key.bytes();
                let (ours, theirs) = match form % 3 {
                    0 => (Ours::new(&key), Theirs::new(&key)),
                    1 => (Ours::from_spki(&key), Theirs::from_spki(&key)),
                    _ => (
                        Ours::from_components(&fips::rsa::PublicKeyComponents {
                            n: &key[..],
                            e: &exponent[..],
                        }),
                        Theirs::from_components(&rind::rsa::PublicKeyComponents {
                            n: &key[..],
                            e: &exponent[..],
                        }),
                    ),
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.as_ref(), theirs.as_ref());
                let i = *algorithm;
                let a = pick(
                    &[
                        &o::PKCS1_SHA256,
                        &o::PKCS1_SHA384,
                        &o::PKCS1_SHA512,
                        &o::PSS_SHA256,
                        &o::PSS_SHA384,
                        &o::PSS_SHA512,
                        &o::legacy::PKCS1_SHA1,
                        &o::legacy::PKCS1_1024_SHA1,
                        &o::legacy::PKCS1_1024_SHA256,
                        &o::legacy::PKCS1_1024_SHA512,
                        &o::legacy::PKCS1_3072_SHA384,
                    ],
                    i,
                );
                let b = pick(
                    &[
                        &t::PKCS1_SHA256,
                        &t::PKCS1_SHA384,
                        &t::PKCS1_SHA512,
                        &t::PSS_SHA256,
                        &t::PSS_SHA384,
                        &t::PSS_SHA512,
                        &t::legacy::PKCS1_SHA1,
                        &t::legacy::PKCS1_1024_SHA1,
                        &t::legacy::PKCS1_1024_SHA256,
                        &t::legacy::PKCS1_1024_SHA512,
                        &t::legacy::PKCS1_3072_SHA384,
                    ],
                    i,
                );
                same_verdict(
                    ours.verify(a, message, signature),
                    theirs.verify(b, message, signature),
                );
            }
            Op::AgreementKey {
                algorithm,
                form,
                bytes,
                peer,
            } => {
                use fips::agreement::PrivateKey as Ours;
                use rind::agreement::PrivateKey as Theirs;
                let i = *algorithm;
                let a = pick(
                    &[
                        &fips::agreement::ECDH_P256,
                        &fips::agreement::ECDH_P384,
                        &fips::agreement::ECDH_P521,
                    ],
                    i,
                );
                let b = pick(
                    &[
                        &rind::agreement::ECDH_P256,
                        &rind::agreement::ECDH_P384,
                        &rind::agreement::ECDH_P521,
                    ],
                    i,
                );
                let bytes = bytes.bytes();
                let (ours, theirs) = match form % 3 {
                    0 => (Ours::from_scalar(a, &bytes), Theirs::from_scalar(b, &bytes)),
                    1 => (Ours::from_pkcs8(a, &bytes), Theirs::from_pkcs8(b, &bytes)),
                    _ => (Ours::from_sec1(a, &bytes), Theirs::from_sec1(b, &bytes)),
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.to_pkcs8().as_ref(), theirs.to_pkcs8().as_ref());
                assert_eq!(ours.to_scalar().as_ref(), theirs.to_scalar().as_ref());
                assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
                let (shared, twin) = (ours.agree(peer), theirs.agree(peer));
                assert_eq!(shared.is_ok(), twin.is_ok());
                agree(shared, twin);
            }
            Op::AgreementPublic {
                algorithm,
                spki,
                bytes,
            } => {
                use fips::agreement::PublicKey as Ours;
                use rind::agreement::PublicKey as Theirs;
                let i = *algorithm;
                let a = pick(
                    &[
                        &fips::agreement::ECDH_P256,
                        &fips::agreement::ECDH_P384,
                        &fips::agreement::ECDH_P521,
                    ],
                    i,
                );
                let b = pick(
                    &[
                        &rind::agreement::ECDH_P256,
                        &rind::agreement::ECDH_P384,
                        &rind::agreement::ECDH_P521,
                    ],
                    i,
                );
                let bytes = bytes.bytes();
                let (ours, theirs) = if *spki {
                    (Ours::from_spki(a, &bytes), Theirs::from_spki(b, &bytes))
                } else {
                    (Ours::new(a, &bytes), Theirs::new(b, &bytes))
                };
                let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
                    return;
                };
                assert_eq!(ours.as_ref(), theirs.as_ref());
                assert_eq!(ours.to_spki().as_ref(), theirs.to_spki().as_ref());
            }
            Op::Encapsulate { set, key } => match set % 3 {
                0 => encapsulate::<fips::kem::MlKem512, rind::kem::MlKem512>(key),
                1 => encapsulate::<fips::kem::MlKem768, rind::kem::MlKem768>(key),
                _ => encapsulate::<fips::kem::MlKem1024, rind::kem::MlKem1024>(key),
            },
            Op::Decapsulate { ciphertext } => {
                // One key per process, as generating one runs its pairwise
                // consistency test.
                static KEY: LazyLock<fips::kem::DecapsulationKey<fips::kem::MlKem768>> =
                    LazyLock::new(|| fips::kem::DecapsulationKey::generate().unwrap());
                let ours = fips::kem::Ciphertext::<fips::kem::MlKem768>::new(ciphertext);
                let theirs = rind::kem::Ciphertext::<rind::kem::MlKem768>::new(ciphertext);
                let (Some(ours), Some(_)) = agree_keys(ours, theirs) else {
                    return;
                };
                // Implicit rejection: any ciphertext of the length decapsulates.
                let _ = KEY.decapsulate(&ours);
            }
            Op::ConstantTime { a, b } => {
                assert_eq!(
                    fips::constant_time::verify(a, b).is_ok(),
                    rind::constant_time::verify(a, b).is_ok()
                );
            }
            Op::Rand { len } => {
                let mut out = vec![0; usize::from(*len)];
                fips::rand::fill(&mut out).unwrap();
            }
        }
    }

    /// Checks that the module loads only keys rind loads, returning both.
    fn agree_keys<A, B>(
        ours: Result<A, fips::Error>,
        theirs: Result<B, rind::Error>,
    ) -> (Option<A>, Option<B>) {
        match (ours, theirs) {
            (Ok(_), Err(error)) => panic!("the module loads what rind refuses: {error:?}"),
            (ours, theirs) => (ours.ok(), theirs.ok()),
        }
    }

    fn keks(
        algorithm: u8,
        kek: &[u8],
    ) -> (
        Result<fips::key_wrap::AesKek, fips::Error>,
        Result<rind::key_wrap::AesKek, rind::Error>,
    ) {
        let a = pick(
            &[
                &fips::key_wrap::AES_128,
                &fips::key_wrap::AES_192,
                &fips::key_wrap::AES_256,
            ],
            algorithm,
        );
        let b = pick(
            &[
                &rind::key_wrap::AES_128,
                &rind::key_wrap::AES_192,
                &rind::key_wrap::AES_256,
            ],
            algorithm,
        );
        (
            fips::key_wrap::AesKek::new(a, kek),
            rind::key_wrap::AesKek::new(b, kek),
        )
    }

    fn ml_dsa_pair<O: fips::ml_dsa::ParameterSet, T: rind::ml_dsa::ParameterSet>(
        seed: &[u8],
        message: &[u8],
    ) {
        let ours = fips::ml_dsa::KeyPair::<O>::from_seed(seed);
        let theirs = rind::ml_dsa::KeyPair::<T>::from_seed(seed);
        let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
            return;
        };
        assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
        assert_eq!(ours.to_pkcs8().as_ref(), theirs.to_pkcs8().as_ref());
        // Signing is hedged: rind verifies the module's.
        let signature = ours.sign(message).unwrap();
        theirs
            .public_key()
            .verify(message, signature.as_ref())
            .unwrap();
    }

    fn ml_dsa_verify<O: fips::ml_dsa::ParameterSet, T: rind::ml_dsa::ParameterSet>(
        spki: bool,
        key: &[u8],
        message: &[u8],
        signature: &[u8],
    ) {
        let (ours, theirs) = if spki {
            (
                fips::ml_dsa::PublicKey::<O>::from_spki(key),
                rind::ml_dsa::PublicKey::<T>::from_spki(key),
            )
        } else {
            (
                fips::ml_dsa::PublicKey::<O>::new(key),
                rind::ml_dsa::PublicKey::<T>::new(key),
            )
        };
        let (Some(ours), Some(theirs)) = agree_keys(ours, theirs) else {
            return;
        };
        same_verdict(
            ours.verify(message, signature),
            theirs.verify(message, signature),
        );
    }

    fn encapsulate<O: fips::kem::Algorithm, T: rind::kem::Algorithm>(key: &[u8]) {
        let ours = fips::kem::EncapsulationKey::<O>::new(key);
        let theirs = rind::kem::EncapsulationKey::<T>::new(key);
        let (Some(ours), Some(_)) = agree_keys(ours, theirs) else {
            return;
        };
        assert_eq!(ours.as_ref(), key);
        ours.encapsulate().unwrap();
    }
}
