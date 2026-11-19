//! rind-aws-lc-rs checked against aws-lc-rs itself: each test runs the same
//! code against both crates, whose names match, and compares the results.

use core::num::NonZeroU32;

use aws_lc_rs as theirs;
use proptest::collection::vec;
use proptest::prelude::*;
use rind_aws_lc_rs as ours;

/// Runs `$body` with `$c` naming rind-aws-lc-rs, then aws-lc-rs, and returns
/// both results.
macro_rules! both {
    (|$c:ident| $body:expr) => {{
        let ours = {
            use rind_aws_lc_rs as $c;
            $body
        };
        let theirs = {
            use aws_lc_rs as $c;
            $body
        };
        (ours, theirs)
    }};
}

/// Asserts that `$body` gives the same result with either crate.
macro_rules! same {
    (|$c:ident| $body:expr) => {{
        let (ours, theirs) = both!(|$c| $body);
        prop_assert_eq!(ours, theirs);
    }};
}

/// A caller's own HKDF output length.
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

proptest! {
    #[test]
    fn digest(algorithm in 0..8usize, data in vec(any::<u8>(), 0..300), split in any::<prop::sample::Index>()) {
        same!(|c| {
            let algorithm = [
                &c::digest::SHA1_FOR_LEGACY_USE_ONLY,
                &c::digest::SHA256,
                &c::digest::SHA384,
                &c::digest::SHA512,
                &c::digest::SHA512_256,
                &c::digest::SHA3_256,
                &c::digest::SHA3_384,
                &c::digest::SHA3_512,
            ][algorithm];
            let (head, tail) = data.split_at(split.index(data.len() + 1));
            let mut context = c::digest::Context::new(algorithm);
            context.update(head);
            context.update(tail);
            (
                c::digest::digest(algorithm, &data).as_ref().to_vec(),
                context.finish().as_ref().to_vec(),
                algorithm.output_len(),
                algorithm.block_len(),
            )
        });
    }

    #[test]
    fn hmac(algorithm in 0..4usize, key in vec(any::<u8>(), 0..200), msg in vec(any::<u8>(), 0..200)) {
        same!(|c| {
            let algorithm = [
                c::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
                c::hmac::HMAC_SHA256,
                c::hmac::HMAC_SHA384,
                c::hmac::HMAC_SHA512,
            ][algorithm];
            let key = c::hmac::Key::new(algorithm, &key);
            let tag = c::hmac::sign(&key, &msg);
            let mut context = c::hmac::Context::with_key(&key);
            context.update(&msg);
            let mut wrong = tag.as_ref().to_vec();
            wrong[0] ^= 1;
            (
                tag.as_ref().to_vec(),
                context.sign().as_ref().to_vec(),
                c::hmac::verify(&key, &msg, tag.as_ref()).is_ok(),
                c::hmac::verify(&key, &msg, &wrong).is_ok(),
            )
        });
    }

    // Lengths from empty up to a few blocks, or either side of each hash's
    // 255-block limit.
    #[test]
    fn hkdf(
        algorithm in 0..4usize,
        salt in vec(any::<u8>(), 0..200),
        ikm in vec(any::<u8>(), 0..200),
        info in vec(vec(any::<u8>(), 0..100), 0..4),
        len in 0..200usize,
        at_limit in any::<bool>(),
    ) {
        let info: Vec<&[u8]> = info.iter().map(Vec::as_slice).collect();
        same!(|c| {
            let algorithm = [
                c::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
                c::hkdf::HKDF_SHA256,
                c::hkdf::HKDF_SHA384,
                c::hkdf::HKDF_SHA512,
            ][algorithm];
            let hash_len = algorithm.hmac_algorithm().digest_algorithm().output_len();
            let len = match at_limit {
                true => 255 * hash_len + len - 100,
                false => len,
            };
            let prk = c::hkdf::Salt::new(algorithm, &salt).extract(&ikm);
            prk.expand(&info, Len(len)).ok().map(|okm| {
                let mut out = vec![0u8; len];
                okm.fill(&mut out).unwrap();
                out
            })
        });
    }

    // Each key an `Okm` becomes, compared by what it then produces.
    #[test]
    fn hkdf_keys(algorithm in 0..4usize, ikm in vec(any::<u8>(), 0..100), msg in vec(any::<u8>(), 0..100)) {
        same!(|c| {
            let algorithm = [
                c::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
                c::hkdf::HKDF_SHA256,
                c::hkdf::HKDF_SHA384,
                c::hkdf::HKDF_SHA512,
            ][algorithm];
            let info: &[&[u8]] = &[b"info"];
            let prk = c::hkdf::Salt::new(algorithm, b"salt").extract(&ikm);
            let mut out = Vec::new();

            for aead in [&c::aead::AES_128_GCM, &c::aead::AES_256_GCM, &c::aead::CHACHA20_POLY1305] {
                let key = c::aead::LessSafeKey::new(c::aead::UnboundKey::from(
                    prk.expand(info, aead).unwrap(),
                ));
                let mut sealed = msg.clone();
                key.seal_in_place_append_tag(
                    c::aead::Nonce::assume_unique_for_key([0; 12]),
                    c::aead::Aad::empty(),
                    &mut sealed,
                )
                .unwrap();
                out.push(sealed);
            }
            for quic in [&c::aead::quic::AES_128, &c::aead::quic::AES_256, &c::aead::quic::CHACHA20] {
                let key = c::aead::quic::HeaderProtectionKey::from(prk.expand(info, quic).unwrap());
                out.push(key.new_mask(&[0x5a; 16]).unwrap().to_vec());
            }
            let key = c::hmac::Key::from(prk.expand(info, algorithm.hmac_algorithm()).unwrap());
            out.push(c::hmac::sign(&key, &msg).as_ref().to_vec());

            let next = c::hkdf::Prk::from(prk.expand(info, algorithm).unwrap());
            let salt = c::hkdf::Salt::from(prk.expand(info, algorithm).unwrap());
            for prk in [next, salt.extract(&msg)] {
                let mut okm = [0u8; 100];
                prk.expand(info, Len(100)).unwrap().fill(&mut okm).unwrap();
                out.push(okm.to_vec());
            }

            let key = c::cipher::UnboundCipherKey::from(prk.expand(info, &c::cipher::AES_256).unwrap());
            let key = c::cipher::EncryptingKey::ctr(key).unwrap();
            let mut in_out = msg.clone();
            let iv = c::iv::FixedLength::from([7u8; 16]);
            key.less_safe_encrypt(&mut in_out, c::cipher::EncryptionContext::Iv128(iv)).unwrap();
            out.push(in_out);
            out
        });
    }

    // Stored values from empty to a few blocks, including those shorter than
    // the hash, which rind-aws-lc-rs compares itself, and a corrupted byte.
    #[test]
    fn pbkdf2(
        algorithm in 0..4usize,
        password in vec(any::<u8>(), 0..100),
        salt in vec(any::<u8>(), 0..100),
        iterations in 1..5u32,
        len in 0..150usize,
        corrupt in any::<prop::sample::Index>(),
    ) {
        let iterations = NonZeroU32::new(iterations).unwrap();
        same!(|c| {
            let algorithm = [
                c::pbkdf2::PBKDF2_HMAC_SHA1,
                c::pbkdf2::PBKDF2_HMAC_SHA256,
                c::pbkdf2::PBKDF2_HMAC_SHA384,
                c::pbkdf2::PBKDF2_HMAC_SHA512,
            ][algorithm];
            let mut stored = vec![0u8; len];
            c::pbkdf2::derive(algorithm, iterations, &salt, &password, &mut stored);
            let verified = c::pbkdf2::verify(algorithm, iterations, &salt, &password, &stored).is_ok();
            let mut corrupted = stored.clone();
            if let Some(byte) = corrupted.get_mut(corrupt.index(len.max(1))) {
                *byte ^= 1;
            }
            let corrupted =
                c::pbkdf2::verify(algorithm, iterations, &salt, &password, &corrupted).is_ok();
            (stored, verified, corrupted || len == 0)
        });
    }

    #[test]
    fn aead(
        algorithm in 0..4usize,
        key in vec(any::<u8>(), 32),
        nonce in any::<[u8; 12]>(),
        aad in vec(any::<u8>(), 0..50),
        msg in vec(any::<u8>(), 0..200),
        corrupt in any::<prop::sample::Index>(),
    ) {
        let (ours_sealed, theirs_sealed) = both!(|c| {
            let algorithm = [
                &c::aead::AES_128_GCM,
                &c::aead::AES_192_GCM,
                &c::aead::AES_256_GCM,
                &c::aead::CHACHA20_POLY1305,
            ][algorithm];
            let key = c::aead::LessSafeKey::new(
                c::aead::UnboundKey::new(algorithm, &key[..algorithm.key_len()]).unwrap(),
            );
            let mut in_out = msg.clone();
            let tag = key
                .seal_in_place_separate_tag(
                    c::aead::Nonce::assume_unique_for_key(nonce),
                    c::aead::Aad::from(&aad),
                    &mut in_out,
                )
                .unwrap();
            in_out.extend_from_slice(tag.as_ref());
            in_out
        });
        prop_assert_eq!(&ours_sealed, &theirs_sealed);

        // Each opens the other's, and refuses it altered.
        let mut corrupted = ours_sealed.clone();
        let index = corrupt.index(corrupted.len());
        corrupted[index] ^= 1;
        same!(|c| {
            let algorithm = [
                &c::aead::AES_128_GCM,
                &c::aead::AES_192_GCM,
                &c::aead::AES_256_GCM,
                &c::aead::CHACHA20_POLY1305,
            ][algorithm];
            let key = c::aead::LessSafeKey::new(
                c::aead::UnboundKey::new(algorithm, &key[..algorithm.key_len()]).unwrap(),
            );
            let open = |sealed: &[u8]| {
                let mut in_out = sealed.to_vec();
                key.open_in_place(
                    c::aead::Nonce::assume_unique_for_key(nonce),
                    c::aead::Aad::from(&aad),
                    &mut in_out,
                )
                .ok()
                .map(|plaintext| plaintext.to_vec())
            };
            // The tag apart, at its full length or one byte short.
            let open_separate = |sealed: &[u8], tag_len: usize| {
                let (ciphertext, tag) = sealed.split_at(sealed.len() - 16);
                let mut in_out = ciphertext.to_vec();
                key.open_in_place_separate_tag(
                    c::aead::Nonce::assume_unique_for_key(nonce),
                    c::aead::Aad::from(&aad),
                    &tag[..tag_len],
                    &mut in_out,
                )
                .ok()
                .map(|plaintext| plaintext.to_vec())
            };
            (
                open(&theirs_sealed),
                open(&corrupted),
                open_separate(&theirs_sealed, 16),
                open_separate(&corrupted, 16),
                open_separate(&theirs_sealed, 15),
            )
        });
    }

    // TLS 1.3 record keys, whose nonces must rise, and TLS 1.2's, whose
    // explicit part must too. A refused seal leaves its buffer as AWS-LC's does.
    #[test]
    fn tls_record_keys(
        tls13 in any::<bool>(),
        aes256 in any::<bool>(),
        mode in 0..3u8,
        extra in vec(any::<u8>(), 1..3),
        key in vec(any::<u8>(), 32),
        start in any::<u64>(),
        steps in vec(0..3u64, 1..6),
        msg in vec(any::<u8>(), 0..64),
    ) {
        same!(|c| {
            let algorithm = match aes256 {
                true => &c::aead::AES_256_GCM,
                false => &c::aead::AES_128_GCM,
            };
            let protocol = match tls13 {
                true => c::aead::TlsProtocolId::TLS13,
                false => c::aead::TlsProtocolId::TLS12,
            };
            let mut key = c::aead::TlsRecordSealingKey::new(algorithm, protocol, &key[..algorithm.key_len()])
                .unwrap();
            let mut counter = start;
            let mut out = Vec::new();
            for step in &steps {
                counter = counter.wrapping_add(*step).wrapping_sub(1);
                let mut nonce = [0x33u8; 12];
                nonce[4..].copy_from_slice(&counter.to_be_bytes());
                let nonce = c::aead::Nonce::assume_unique_for_key(nonce);
                let mut in_out = msg.clone();
                let sealed = match mode {
                    0 => key.seal_in_place_append_tag(nonce, c::aead::Aad::empty(), &mut in_out),
                    1 => key
                        .seal_in_place_separate_tag(nonce, c::aead::Aad::empty(), &mut in_out)
                        .map(|tag| in_out.extend_from_slice(tag.as_ref())),
                    // Prefilled outputs show what a refused seal leaves in them.
                    _ => {
                        let mut tail = vec![0x55; extra.len() + algorithm.tag_len()];
                        in_out.fill(0x55);
                        let sealed = key.seal_out_of_place_scatter(
                            nonce,
                            c::aead::Aad::empty(),
                            &msg,
                            &mut in_out,
                            &extra,
                            &mut tail,
                        );
                        in_out.extend_from_slice(&tail);
                        sealed
                    }
                };
                out.push((sealed.is_ok(), in_out));
            }
            out
        });
    }

    #[test]
    fn nonce_sequences(identifier in any::<[u8; 8]>(), limit in 0..4u32, start in any::<u32>()) {
        same!(|c| {
            use c::aead::NonceSequence;
            let mut counter = c::aead::nonce_sequence::Counter32Builder::new()
                .identifier(identifier)
                .limit(limit)
                .counter(start)
                .build();
            (0..5)
                .map(|_| counter.advance().ok().map(|nonce| nonce.as_ref().to_vec()))
                .collect::<Vec<_>>()
        });
    }

    #[test]
    fn cipher(
        algorithm in 0..3usize,
        key in vec(any::<u8>(), 32),
        iv in any::<[u8; 16]>(),
        blocks in 0..5usize,
        msg in vec(any::<u8>(), 0..80),
    ) {
        same!(|c| {
            let (algorithm, key_len) = [
                (&c::cipher::AES_128, 16),
                (&c::cipher::AES_192, 24),
                (&c::cipher::AES_256, 32),
            ][algorithm];
            let key = || c::cipher::UnboundCipherKey::new(algorithm, &key[..key_len]).unwrap();
            let context = || c::cipher::EncryptionContext::Iv128(c::iv::FixedLength::from(iv));

            let mut ctr = msg.clone();
            let ctr_key = c::cipher::EncryptingKey::ctr(key()).unwrap();
            let decryption = ctr_key.less_safe_encrypt(&mut ctr, context()).unwrap();
            let mut ctr_round = ctr.clone();
            c::cipher::DecryptingKey::ctr(key())
                .unwrap()
                .decrypt(&mut ctr_round, decryption)
                .unwrap();

            let mut cbc = vec![0x42u8; 16 * blocks];
            let cbc_key = c::cipher::EncryptingKey::cbc(key()).unwrap();
            cbc_key.less_safe_encrypt(&mut cbc, context()).unwrap();

            let mut padded = msg.clone();
            let padded_key = c::cipher::PaddedBlockEncryptingKey::cbc_pkcs7(key()).unwrap();
            let decryption = padded_key.less_safe_encrypt(&mut padded, context()).unwrap();
            let mut padded_round = padded.clone();
            let plaintext = c::cipher::PaddedBlockDecryptingKey::cbc_pkcs7(key())
                .unwrap()
                .decrypt(&mut padded_round, decryption)
                .unwrap()
                .to_vec();
            (ctr, ctr_round == msg, cbc, padded, plaintext == msg)
        });
    }

    #[test]
    fn key_wrap(aes256 in any::<bool>(), kek in vec(any::<u8>(), 32), key in vec(any::<u8>(), 1..64), corrupt in any::<prop::sample::Index>()) {
        same!(|c| {
            use c::key_wrap::{KeyWrap, KeyWrapPadded};
            let (cipher, kek) = match aes256 {
                true => (&c::key_wrap::AES_256, &kek[..32]),
                false => (&c::key_wrap::AES_128, &kek[..16]),
            };
            let kek = || c::key_wrap::AesKek::new(cipher, kek).unwrap();

            let mut wrapped = [0u8; 80];
            let wrapped = kek().wrap(&key, &mut wrapped).ok().map(|w| w.to_vec());
            let unwrapped = wrapped.as_ref().and_then(|wrapped| {
                let mut out = [0u8; 80];
                kek().unwrap(wrapped, &mut out).ok().map(|k| k.to_vec())
            });

            let mut padded = [0u8; 80];
            let padded = kek().wrap_with_padding(&key, &mut padded).unwrap().to_vec();
            let mut out = [0u8; 80];
            let unpadded = kek().unwrap_with_padding(&padded, &mut out).unwrap().to_vec();
            let mut corrupted = padded.clone();
            let index = corrupt.index(corrupted.len());
            corrupted[index] ^= 1;
            let mut out = [0u8; 80];
            let corrupted = kek().unwrap_with_padding(&corrupted, &mut out).is_ok();
            (wrapped, unwrapped, padded, unpadded, corrupted)
        });
    }
}

/// Scatter buffers of the wrong length leave the TLS nonce unused.
#[test]
fn tls_scatter_keeps_nonce() {
    let results = both!(|c| {
        use c::aead::{AES_128_GCM, Aad, Nonce, TlsProtocolId, TlsRecordSealingKey};
        let mut key =
            TlsRecordSealingKey::new(&AES_128_GCM, TlsProtocolId::TLS13, &[7; 16]).unwrap();
        let mut seal = |out_len: usize| {
            let mut out = vec![0; out_len];
            let mut tag = [0; 16];
            key.seal_out_of_place_scatter(
                Nonce::assume_unique_for_key([1; 12]),
                Aad::empty(),
                b"message",
                &mut out,
                &[],
                &mut tag,
            )
            .is_ok()
        };
        (seal(3), seal(7))
    });
    assert_eq!(results, ((false, true), (false, true)));
}

/// An RSA key outside a verification algorithm's modulus range parses, then
/// verifies nothing, on both sides of each algorithm's range, while a key in
/// range verifies.
#[test]
fn rsa_range_at_verify() {
    use theirs::signature::{self as sig, KeyPair as _, RsaKeyPair};
    // aws-lc-rs signs neither with SHA-1 nor with a key under 2048 bits, so
    // those signatures over "message" come from OpenSSL, in
    // tests/data/rsa-range as `<bits>-<tag>.sig`. No PSS-SHA-512 signature
    // with a salt as long as the hash fits a 1024-bit key.
    let fixture = |bits: usize, tag: &str| {
        if (bits, tag) == (1024, "pss-sha512") {
            return None;
        }
        let path = format!(
            "{}/tests/data/rsa-range/{bits}-{tag}.sig",
            env!("CARGO_MANIFEST_DIR")
        );
        Some(std::fs::read(&path).unwrap_or_else(|err| panic!("{path}: {err}")))
    };
    let signers = [
        &include_bytes!("aws-lc-rs/data/rsa_test_private_key_2048.p8")[..],
        include_bytes!("aws-lc-rs/data/rsa_test_private_key_8192.p8"),
    ]
    .map(|der| RsaKeyPair::from_pkcs8(der).unwrap());
    let small = include_bytes!("aws-lc-rs/data/rsa_test_public_key_1024.x509");
    let keys = [
        (theirs::rsa::PublicKey::from_der(small).unwrap(), None),
        (signers[0].public_key().clone(), Some(&signers[0])),
        (signers[1].public_key().clone(), Some(&signers[1])),
    ];
    // Each verification algorithm, its smallest modulus, its fixture tag, and
    // the encoding aws-lc-rs signs for it with, if any.
    let algorithms: [(&str, usize, &str, Option<&'static dyn sig::RsaEncoding>); 11] = [
        (
            "RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY",
            1024,
            "sha1",
            None,
        ),
        (
            "RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY",
            1024,
            "sha256",
            Some(&sig::RSA_PKCS1_SHA256),
        ),
        (
            "RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY",
            1024,
            "sha512",
            Some(&sig::RSA_PKCS1_SHA512),
        ),
        (
            "RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY",
            2048,
            "sha1",
            None,
        ),
        (
            "RSA_PKCS1_2048_8192_SHA256",
            2048,
            "sha256",
            Some(&sig::RSA_PKCS1_SHA256),
        ),
        (
            "RSA_PKCS1_2048_8192_SHA384",
            2048,
            "sha384",
            Some(&sig::RSA_PKCS1_SHA384),
        ),
        (
            "RSA_PKCS1_2048_8192_SHA512",
            2048,
            "sha512",
            Some(&sig::RSA_PKCS1_SHA512),
        ),
        (
            "RSA_PKCS1_3072_8192_SHA384",
            3072,
            "sha384",
            Some(&sig::RSA_PKCS1_SHA384),
        ),
        (
            "RSA_PSS_2048_8192_SHA256",
            2048,
            "pss-sha256",
            Some(&sig::RSA_PSS_SHA256),
        ),
        (
            "RSA_PSS_2048_8192_SHA384",
            2048,
            "pss-sha384",
            Some(&sig::RSA_PSS_SHA384),
        ),
        (
            "RSA_PSS_2048_8192_SHA512",
            2048,
            "pss-sha512",
            Some(&sig::RSA_PSS_SHA512),
        ),
    ];
    let rng = theirs::rand::SystemRandom::new();
    for (key, signer) in &keys {
        let public = key.as_ref();
        let n = key.modulus().big_endian_without_leading_zero();
        let e = key.exponent().big_endian_without_leading_zero();
        let bits = key.modulus_len() * 8;
        for (name, min_bits, tag, encoding) in algorithms {
            let signature = match (signer, encoding) {
                (Some(signer), Some(encoding)) => {
                    let mut signature = vec![0; key.modulus_len()];
                    signer
                        .sign(encoding, &rng, b"message", &mut signature)
                        .unwrap();
                    Some(signature)
                }
                _ => fixture(bits, tag),
            };
            let valid = signature.is_some();
            let signature = signature.unwrap_or_else(|| vec![0; key.modulus_len()]);
            let results = both!(|c| {
                use c::signature as s;
                let algorithm: &'static s::RsaParameters = match name {
                    "RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY" => {
                        &s::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY
                    }
                    "RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY" => {
                        &s::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY
                    }
                    "RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY" => {
                        &s::RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY
                    }
                    "RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY" => {
                        &s::RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY
                    }
                    "RSA_PKCS1_2048_8192_SHA256" => &s::RSA_PKCS1_2048_8192_SHA256,
                    "RSA_PKCS1_2048_8192_SHA384" => &s::RSA_PKCS1_2048_8192_SHA384,
                    "RSA_PKCS1_2048_8192_SHA512" => &s::RSA_PKCS1_2048_8192_SHA512,
                    "RSA_PKCS1_3072_8192_SHA384" => &s::RSA_PKCS1_3072_8192_SHA384,
                    "RSA_PSS_2048_8192_SHA256" => &s::RSA_PSS_2048_8192_SHA256,
                    "RSA_PSS_2048_8192_SHA384" => &s::RSA_PSS_2048_8192_SHA384,
                    _ => &s::RSA_PSS_2048_8192_SHA512,
                };
                let parsed = s::ParsedPublicKey::new(algorithm, public).unwrap();
                let unparsed = s::UnparsedPublicKey::new(algorithm, public);
                let components = s::RsaPublicKeyComponents { n, e }
                    .to_parsed_public_key(algorithm)
                    .unwrap();
                [
                    parsed.verify_sig(b"message", &signature).is_ok(),
                    unparsed
                        .parse()
                        .unwrap()
                        .verify_sig(b"message", &signature)
                        .is_ok(),
                    unparsed.verify(b"message", &signature).is_ok(),
                    components.verify_sig(b"message", &signature).is_ok(),
                ]
            });
            let expected = valid && bits >= min_bits;
            assert_eq!(
                results.1, [expected; 4],
                "aws-lc-rs: {name} with a {bits}-bit key"
            );
            assert_eq!(results.0, results.1, "{name} with a {bits}-bit key");
        }
    }
}
