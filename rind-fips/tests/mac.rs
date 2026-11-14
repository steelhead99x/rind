// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! HMAC, HKDF, and PBKDF2 through the module agree with rind's, which its
//! own tests check against Wycheproof and aws-lc-rs, and PBKDF2 refuses
//! what SP 800-132 does not approve.
#![cfg(rind_fips_module)]

use std::num::NonZeroU32;

use rind_fips::{Error, hkdf, hmac, pbkdf2};

/// `len` bytes that differ for each `seed`.
fn bytes(seed: &str, len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    let mut counter = 0u32;
    while out.len() < len {
        let mut ctx = rind::digest::Context::new(&rind::digest::SHA256);
        ctx.update(seed.as_bytes());
        ctx.update(&counter.to_be_bytes());
        out.extend_from_slice(ctx.finish().as_ref());
        counter += 1;
    }
    out.truncate(len);
    out
}

const HMACS: [(&hmac::Algorithm, &rind::hmac::Algorithm); 4] = [
    (&hmac::legacy::HMAC_SHA1, &rind::hmac::legacy::HMAC_SHA1),
    (&hmac::HMAC_SHA256, &rind::hmac::HMAC_SHA256),
    (&hmac::HMAC_SHA384, &rind::hmac::HMAC_SHA384),
    (&hmac::HMAC_SHA512, &rind::hmac::HMAC_SHA512),
];

#[test]
fn hmac_matches_rind() {
    for (ours, theirs) in HMACS {
        assert_eq!(ours.tag_len(), theirs.tag_len());
        // Empty, short, a block, and longer than a block, which HMAC hashes.
        for key_len in [0, 1, 32, 64, 65, 128, 129, 200] {
            let key_value = bytes("key", key_len);
            let key = hmac::Key::new(ours, &key_value);
            let reference = rind::hmac::Key::new(theirs, &key_value);
            assert!(core::ptr::eq(key.algorithm(), ours));

            for data_len in [0, 1, 63, 64, 65, 127, 128, 129, 1000] {
                let data = bytes("data", data_len);
                let expected = rind::hmac::sign(&reference, &data);
                let tag = hmac::sign(&key, &data);
                assert_eq!(
                    tag.as_ref(),
                    expected.as_ref(),
                    "{ours:?}, key {key_len}, data {data_len}"
                );
                assert_eq!(hmac::sign(&key.clone(), &data).as_ref(), expected.as_ref());

                let (head, tail) = data.split_at(data_len / 3);
                let mut ctx = hmac::Context::with_key(&key);
                ctx.update(head);
                let fork = ctx.clone();
                ctx.update(tail);
                assert_eq!(ctx.sign().as_ref(), expected.as_ref());
                let mut fork = fork;
                fork.update(tail);
                assert_eq!(fork.sign().as_ref(), expected.as_ref());

                hmac::verify(&key, &data, tag.as_ref()).unwrap();
                let mut flipped = tag.as_ref().to_vec();
                let at = data_len % flipped.len();
                flipped[at] ^= 1;
                assert_eq!(
                    hmac::verify(&key, &data, &flipped),
                    Err(Error::BadSignature)
                );
                let truncated = &tag.as_ref()[..tag.as_ref().len() - 1];
                assert_eq!(
                    hmac::verify(&key, &data, truncated),
                    Err(Error::BadSignature)
                );
            }
        }
    }
}

const HKDFS: [(&hkdf::Algorithm, &rind::hkdf::Algorithm, usize); 4] = [
    (&hkdf::legacy::HKDF_SHA1, &rind::hkdf::legacy::HKDF_SHA1, 20),
    (&hkdf::HKDF_SHA256, &rind::hkdf::HKDF_SHA256, 32),
    (&hkdf::HKDF_SHA384, &rind::hkdf::HKDF_SHA384, 48),
    (&hkdf::HKDF_SHA512, &rind::hkdf::HKDF_SHA512, 64),
];

#[test]
fn hkdf_matches_rind() {
    for (ours, theirs, hash_len) in HKDFS {
        for salt_len in [0, 13, 80] {
            let salt_value = bytes("salt", salt_len);
            let salt = hkdf::Salt::new(ours, &salt_value);
            let reference_salt = rind::hkdf::Salt::new(theirs, &salt_value);
            for secret_len in [0, 22, 100] {
                let secret = bytes("secret", secret_len);
                let reference = reference_salt.extract(&secret).unwrap();
                // FIPS 140-3 approves no empty salt, which rind takes.
                if salt_len == 0 {
                    assert_eq!(salt.extract(&secret).unwrap_err(), Error::WrongLength);
                    continue;
                }
                let prk = salt.extract(&secret).unwrap();

                // Nor an empty info, however it is split.
                for info in [&[][..], &[&[][..]], &[&[][..], &[][..]]] {
                    assert_eq!(prk.expand(info, 16).unwrap_err(), Error::WrongLength);
                    assert_eq!(
                        prk.expand(info, &hmac::HMAC_SHA256).unwrap_err(),
                        Error::WrongLength
                    );
                    assert_eq!(
                        prk.expand(info, &hkdf::HKDF_SHA256).unwrap_err(),
                        Error::WrongLength
                    );
                    assert!(reference.expand(info, 16).is_ok());
                }

                let (a, b) = (bytes("a", 10), bytes("b", 300));
                let infos: [&[&[u8]]; 3] = [&[&a], &[&[], &a], &[&a, &b]];
                for info in infos {
                    for len in [1, hash_len, hash_len + 1, 255 * hash_len] {
                        let mut out = vec![0; len];
                        let mut expected = vec![0; len];
                        prk.expand(info, len).unwrap().fill(&mut out).unwrap();
                        reference
                            .expand(info, len)
                            .unwrap()
                            .fill(&mut expected)
                            .unwrap();
                        assert_eq!(
                            out, expected,
                            "{ours:?}, salt {salt_len}, secret {secret_len}"
                        );
                    }

                    // Into an HMAC key, and into a further PRK.
                    for (hmac_ours, hmac_theirs) in HMACS {
                        let key = hmac::Key::from(prk.expand(info, hmac_ours).unwrap());
                        let reference_key =
                            rind::hmac::Key::from(reference.expand(info, hmac_theirs).unwrap());
                        assert_eq!(
                            hmac::sign(&key, b"message").as_ref(),
                            rind::hmac::sign(&reference_key, b"message").as_ref()
                        );
                    }
                    for (next_ours, next_theirs, _) in HKDFS {
                        let next = hkdf::Prk::from(prk.expand(info, next_ours).unwrap());
                        let reference_next =
                            rind::hkdf::Prk::from(reference.expand(info, next_theirs).unwrap());
                        let (mut out, mut expected) = ([0; 42], [0; 42]);
                        next.expand(&[b"next"], 42).unwrap().fill(&mut out).unwrap();
                        reference_next
                            .expand(&[b"next"], 42)
                            .unwrap()
                            .fill(&mut expected)
                            .unwrap();
                        assert_eq!(out, expected);
                    }
                }

                // Beyond 255 blocks, or not the length expanded for.
                let info: [&[u8]; 1] = [b"info"];
                assert_eq!(
                    prk.expand(&info, 255 * hash_len + 1).unwrap_err(),
                    Error::WrongLength
                );
                assert_eq!(
                    prk.expand(&info, 31).unwrap().fill(&mut [0; 32]),
                    Err(Error::WrongLength)
                );
            }
        }
    }
}

const PBKDF2S: [(&pbkdf2::Algorithm, &rind::pbkdf2::Algorithm, usize); 4] = [
    (
        &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        &rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        20,
    ),
    (
        &pbkdf2::PBKDF2_HMAC_SHA256,
        &rind::pbkdf2::PBKDF2_HMAC_SHA256,
        32,
    ),
    (
        &pbkdf2::PBKDF2_HMAC_SHA384,
        &rind::pbkdf2::PBKDF2_HMAC_SHA384,
        48,
    ),
    (
        &pbkdf2::PBKDF2_HMAC_SHA512,
        &rind::pbkdf2::PBKDF2_HMAC_SHA512,
        64,
    ),
];

#[test]
fn pbkdf2_matches_rind() {
    let iterations = NonZeroU32::new(1000).unwrap();
    for (ours, theirs, hash_len) in PBKDF2S {
        for password_len in [14, 64, 200] {
            let password = bytes("password", password_len);
            let secret = pbkdf2::Secret::new(ours, &password);
            let reference = rind::pbkdf2::Secret::new(theirs, &password);
            for salt_len in [16, 33] {
                let salt = bytes("salt", salt_len);
                for len in [14, hash_len, hash_len + 1, 3 * hash_len] {
                    let mut out = vec![0; len];
                    let mut expected = vec![0; len];
                    secret.derive(iterations, &salt, &mut out).unwrap();
                    reference.derive(iterations, &salt, &mut expected).unwrap();
                    assert_eq!(
                        out, expected,
                        "{ours:?}, password {password_len}, salt {salt_len}"
                    );

                    if len >= hash_len {
                        secret.verify(iterations, &salt, &out).unwrap();
                        out[len - 1] ^= 1;
                        assert_eq!(
                            secret.verify(iterations, &salt, &out),
                            Err(Error::BadSignature)
                        );
                    } else {
                        // Easier to match than the whole hash, as in rind.
                        assert_eq!(
                            secret.verify(iterations, &salt, &out),
                            Err(Error::WrongLength)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn pbkdf2_refuses_what_sp_800_132_does_not_approve() {
    let iterations = NonZeroU32::new(1000).unwrap();
    let secret = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, &[1; 14]);
    let salt = [2; 16];
    let mut out = [0; 32];
    secret.derive(iterations, &salt, &mut out).unwrap();

    let short = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, &[1; 13]);
    let few = NonZeroU32::new(999).unwrap();
    let refused = [
        short.derive(iterations, &salt, &mut [0; 32]),
        short.verify(iterations, &salt, &out),
        secret.derive(iterations, &salt[..15], &mut [0; 32]),
        secret.verify(iterations, &salt[..15], &out),
        secret.derive(few, &salt, &mut [0; 32]),
        secret.verify(few, &salt, &out),
        secret.derive(iterations, &salt, &mut [0; 13]),
    ];
    for (i, result) in refused.into_iter().enumerate() {
        assert_eq!(result, Err(Error::WrongLength), "case {i}");
    }
}
