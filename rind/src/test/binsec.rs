// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The harnesses `admin/ct-binsec` checks under BINSEC: each runs one
//! primitive's secret paths through the public API in a single checked
//! region. A key is secret from where rind marks it, once parsed, and a
//! harness marks the other secrets it passes, such as a plaintext. A
//! harness ignores what a declassified check returns, since BINSEC takes
//! both of its values.

use core::hint::black_box;

use crate::low::ct;
use crate::low::ct_binsec::{checked, length};

/// `N` bytes of `fill`, marked secret.
fn secret<const N: usize>(fill: u8) -> [u8; N] {
    let bytes = [fill; N];
    ct::secret_slice(&bytes);
    bytes
}

// Messages take a whole block, then a partial one, through each cipher's
// tail handling. ChaCha20's take every length up to that; BINSEC cannot
// explore each length of the others in a scheduled run's time, where it reaches
// software AES, `malloc`, or a hash's buffering.
const MESSAGE: usize = 75;

// Not on aarch64, where BINSEC cannot finish the NEON GHASH that runs
// without PMULL in a scheduled run's time.
#[cfg(not(rind_backend = "aarch64"))]
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_aes_gcm() {
    use crate::aead::*;

    checked(|| {
        for algorithm in [&AES_128_GCM, &AES_192_GCM, &AES_256_GCM] {
            let key = Key::new(algorithm, &secret::<32>(1)[..algorithm.key_len()]).unwrap();
            let nonce = || Nonce::assume_unique_for_key([2; 12]);
            let mut msg = secret::<MESSAGE>(3);
            let tag = key
                .seal_in_place_separate_tag(nonce(), &[4; 21], &mut msg)
                .unwrap();
            black_box(
                key.open_in_place_separate_tag(nonce(), &[4; 21], tag, &mut msg)
                    .is_ok(),
            );
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_chacha20_poly1305() {
    use crate::aead::*;

    checked(|| {
        let key = Key::new(&CHACHA20_POLY1305, &secret::<32>(1)).unwrap();
        let nonce = || Nonce::assume_unique_for_key([2; 12]);
        let mut msg = secret::<MESSAGE>(3);
        let msg = &mut msg[..length(MESSAGE)];
        let tag = key
            .seal_in_place_separate_tag(nonce(), &[4; 21], msg)
            .unwrap();
        black_box(
            key.open_in_place_separate_tag(nonce(), &[4; 21], tag, msg)
                .is_ok(),
        );
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_xchacha20_poly1305() {
    use crate::aead::*;

    checked(|| {
        let key = RandomizedNonceKey::new(&secret::<32>(1));
        let mut msg = secret::<MESSAGE>(3).to_vec();
        let nonce = key.seal_in_place_append_tag(&[4; 21], &mut msg).unwrap();
        black_box(key.open_in_place(nonce, &[4; 21], &mut msg).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_quic_header_protection() {
    use crate::aead::quic::*;

    checked(|| {
        for algorithm in [&AES_128, &AES_256, &CHACHA20] {
            let key = HeaderProtectionKey::new(algorithm, &secret::<32>(1)[..algorithm.key_len()]);
            key.unwrap().mask(&[2; SAMPLE_LEN]);
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_aes() {
    use crate::cipher::*;

    checked(|| {
        for algorithm in [&AES_128, &AES_192, &AES_256] {
            let key = &secret::<32>(1)[..algorithm.key_len];
            Aes::new(algorithm, key)
                .unwrap()
                .encrypt_block(&mut secret(2));
            let ctr = AesCtr::new(algorithm, key, 32).unwrap();
            ctr.apply_keystream(&[3; 16], &mut secret::<MESSAGE>(4))
                .unwrap();
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_aes_cbc() {
    use crate::cipher::*;

    checked(|| {
        for algorithm in [&AES_128, &AES_192, &AES_256] {
            let key = &secret::<32>(1)[..algorithm.key_len];
            let mut msg = secret::<MESSAGE>(2).to_vec();
            let iv = CbcIv::assume_unpredictable([3; 16]);
            let encrypting = AesCbcEncryptingKey::new(algorithm, key).unwrap();
            encrypting.encrypt(iv, &mut msg).unwrap();
            let decrypting = AesCbcDecryptingKey::new(algorithm, key).unwrap();
            black_box(decrypting.decrypt(&[3; 16], &mut msg).is_ok());
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_chacha20() {
    use crate::cipher::*;

    checked(|| {
        // Eight blocks through x86_64's verified-garbage routine and a tail,
        // then every shorter length, each of which takes its own path.
        let key = ChaCha20::new(&secret(1));
        key.apply_keystream(&[2; 12], 3, &mut secret::<{ 512 + MESSAGE }>(4))
            .unwrap();
        let mut msg = secret::<MESSAGE>(4);
        key.apply_keystream(&[2; 12], 3, &mut msg[..length(MESSAGE)])
            .unwrap();
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_aes_kw() {
    use crate::key_wrap::*;

    checked(|| {
        for algorithm in [&AES_128, &AES_192, &AES_256] {
            let kek = AesKek::new(algorithm, &secret::<32>(1)[..algorithm.key_len]).unwrap();
            let (mut wrapped, mut key) = ([0; 24], [0; 16]);
            kek.wrap_key(Mode::Kw, &secret::<16>(2), &mut wrapped)
                .unwrap();
            black_box(kek.unwrap_key(Mode::Kw, &wrapped, &mut key).is_ok());
            // The key buffer is 8 bytes shorter than the wrapped key, as
            // unwrapping requires, so the unwrap runs rather than refusing
            // the length.
            let (mut wrapped, mut key) = ([0; 32], [0; 24]);
            kek.wrap_key(Mode::Kwp, &secret::<20>(2), &mut wrapped)
                .unwrap();
            black_box(kek.unwrap_key(Mode::Kwp, &wrapped, &mut key).is_ok());
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_digest() {
    use crate::digest::*;

    checked(|| {
        for algorithm in [&legacy::MD5, &legacy::SHA1, &SHA256, &SHA384, &SHA512]
            .into_iter()
            .chain([&SHA512_256, &SHA3_256, &SHA3_384, &SHA3_512])
        {
            black_box(digest(algorithm, &secret::<150>(1)));
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_hmac() {
    use crate::hmac::*;

    checked(|| {
        for algorithm in [&legacy::HMAC_SHA1, &HMAC_SHA256, &HMAC_SHA384, &HMAC_SHA512] {
            let key = Key::new(algorithm, &secret::<200>(1));
            let tag = sign(&key, &secret::<150>(2));
            black_box(verify(&key, &secret::<150>(2), tag.as_ref()).is_ok());
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_hkdf() {
    use crate::hkdf::*;

    checked(|| {
        let prk = Salt::new(&HKDF_SHA256, &[1; 32])
            .extract(&secret::<32>(2))
            .unwrap();
        let mut okm = [0; 80];
        prk.fill(&[b"info"], &mut okm).unwrap();
        Prk::new(&HKDF_SHA256, &secret::<32>(3))
            .fill(&[b"info"], &mut okm)
            .unwrap();
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_pbkdf2() {
    use crate::pbkdf2::*;

    checked(|| {
        let secret = Secret::new(&PBKDF2_HMAC_SHA256, &secret::<20>(1));
        let mut out = [0; 40];
        let iterations = core::num::NonZeroU32::new(2).unwrap();
        secret.derive(iterations, &[2; 16], &mut out).unwrap();
        black_box(secret.verify(iterations, &[2; 16], &out).is_ok());
    });
}

// Not on aarch64, where BINSEC cannot finish it in a nightly's time. Its
// portable kernels pass here on the portable backend, and ctgrind's arm64
// rows run `high::argon2::secret_password`.
#[cfg(not(rind_backend = "aarch64"))]
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_argon2() {
    use crate::argon2::*;

    // The least memory, in one lane: two blocks of each slice, so both
    // halves of the first pass, and a second pass, run in a short search.
    // The data-dependent references are declassified, as Argon2id's
    // exception to the constant-time rule allows.
    let params = Params::new(8, 2, 1).unwrap();
    checked(|| {
        let password = Secret::new(&secret::<20>(1));
        let mut out = [0; 32];
        password.derive(params, &[2; 16], &mut out).unwrap();
        black_box(password.verify(params, &[2; 16], &out).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_x25519() {
    use crate::agreement::*;

    let peer = PrivateKey::from_scalar(&X25519, &[7; 32]).unwrap();
    let peer = peer.public_key().as_ref().to_vec();
    checked(|| {
        let key = PrivateKey::from_scalar(&X25519, &[1; 32]).unwrap();
        black_box(key.agree(&peer).is_ok());
    });
}

fn ecdh(algorithm: &'static crate::agreement::Algorithm, len: usize) {
    use crate::agreement::*;

    // Each scalar is below its curve's order, P-521's having a top byte of 1.
    let mut scalar = vec![1; len];
    scalar[len - 1] = 2;
    let peer = PrivateKey::from_scalar(algorithm, &scalar).unwrap();
    let peer = peer.public_key().as_ref().to_vec();
    checked(|| {
        let key = PrivateKey::from_scalar(algorithm, &vec![1; len]).unwrap();
        black_box(key.agree(&peer).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdh_p256() {
    ecdh(&crate::agreement::ECDH_P256, 32);
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdh_p384() {
    ecdh(&crate::agreement::ECDH_P384, 48);
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdh_p521() {
    ecdh(&crate::agreement::ECDH_P521, 66);
}

fn mlkem<P: crate::mid::mlkem::Params>() {
    use crate::mid::mlkem::DecapKey;

    let (_, ciphertext) = DecapKey::<P>::keygen_internal(&[1; 64])
        .encapsulation_key()
        .encaps()
        .unwrap();
    checked(|| DecapKey::<P>::keygen_internal(&[1; 64]).decaps(&ciphertext));
}

// ML-KEM-512 samples its key's noise with `eta1 = 3`, and ML-KEM-1024
// compresses its re-encryption to 11 and 5 bits.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mlkem512() {
    mlkem::<crate::mid::mlkem::MlKem512>();
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mlkem768() {
    mlkem::<crate::mid::mlkem::MlKem768>();
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mlkem1024() {
    mlkem::<crate::mid::mlkem::MlKem1024>();
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ed25519() {
    use crate::ed25519::*;

    checked(|| {
        let key = KeyPair::from_seed(&[1; 32]).unwrap();
        key.sign(&secret::<40>(2))
    });
}

fn ecdsa(algorithm: &'static crate::ecdsa::SigningAlgorithm, pkcs8: &[u8]) {
    use crate::ecdsa::*;

    checked(|| {
        let key = KeyPair::from_pkcs8(algorithm, pkcs8).unwrap();
        black_box(key.sign(&secret::<40>(1)).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p256() {
    use crate::ecdsa::sign::P256_SHA256_FIXED;
    ecdsa(
        &P256_SHA256_FIXED,
        include_bytes!("../high/ecdsa/secp256r1.pkcs8.der"),
    );
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p384() {
    use crate::ecdsa::sign::P384_SHA384_FIXED;
    ecdsa(
        &P384_SHA384_FIXED,
        include_bytes!("../high/ecdsa/secp384r1.pkcs8.der"),
    );
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p521() {
    use crate::ecdsa::sign::P521_SHA512_FIXED;
    ecdsa(
        &P521_SHA512_FIXED,
        include_bytes!("../high/ecdsa/secp521r1.pkcs8.der"),
    );
}

// The 16-word Montgomery product RSA-2048's CRT exponentiation runs.
// On a narrow aarch64 multiplier that is `bignum_kmul_16_32`,
// `bignum_ksqr_16_32`, and `bignum_emontredc_8n`. `admin/ct-binsec` runs
// this again with `RIND_CPU_DISABLE_wide_mul=1` on aarch64, because a wide
// host's own schedule is `_alt` and `bn_mul_mont`.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mont16() {
    use crate::low::{mont_mul, mont_sqr};

    checked(|| {
        let (x, mut y, mut z) = ([1u64; 16], [2u64; 16], [0u64; 16]);
        let m = [u64::MAX; 16];
        ct::secret_slice(&x);
        ct::secret_slice(&y);
        ct::secret_slice(&m);
        let n0 = ct::into_secret(1u64);
        mont_mul(&mut z, &x, &y, &m, n0);
        mont_sqr(&mut y, &z, &m, n0);
        black_box(&y);
    });
}

// The Montgomery products RSA-4096's private operation runs at its CRT
// width, 32 words: s2n-bignum's Karatsuba routines and aws-lc's
// `bn_mul4x_mont` and `bn_sqr8x_mont` on x86_64. BINSEC cannot finish the
// exponentiation that runs thousands of them, whose other code
// `ct_binsec_rsa2048_sign` checks at 16 words. On a wide aarch64 host that
// sign takes `bn_mul_mont`, so the 16-word Karatsuba path is
// `ct_binsec_mont16` with the narrow schedule forced.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mont_mul() {
    use crate::low::{mont_mul, mont_sqr};

    checked(|| {
        let (x, mut y, mut z) = ([1u64; 32], [2u64; 32], [0u64; 32]);
        // CRT's modulus is a private prime, and its `-m^-1 mod 2^64` with
        // it; the concrete values are an odd modulus and its 1.
        let m = [u64::MAX; 32];
        ct::secret_slice(&x);
        ct::secret_slice(&y);
        ct::secret_slice(&m);
        let n0 = ct::into_secret(1u64);
        mont_mul(&mut z, &x, &y, &m, n0);
        mont_sqr(&mut y, &z, &m, n0);
        black_box(&y);
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_constant_time_verify() {
    black_box(checked(|| {
        crate::constant_time::verify(&secret::<33>(1), &secret::<33>(2)).is_ok()
    }));
}

// RSA's whole private operation, from loading the key, whose check reduces
// the private exponent, through the CRT exponentiations and recombination to
// the padding. RSA-2048's 16-word primes take x86_64's Karatsuba products
// and AVX2 gather, and RSA-3072's 24 its `bn_power5`.
fn rsa_sign(pkcs8: &[u8]) {
    use crate::rsa::*;

    checked(|| {
        let key = KeyPair::from_pkcs8(pkcs8).unwrap();
        black_box(key.sign(&sign::PKCS1_SHA256, &[1; 40]).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa2048_sign() {
    rsa_sign(include_bytes!("../high/rsa/rsa2048.pkcs8.der"));
}

// Only x86_64 runs other code at 24 words than at 16.
#[cfg(rind_backend = "x86_64")]
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa3072_sign() {
    rsa_sign(include_bytes!("../high/rsa/rsa3072.pkcs8.der"));
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa2048_oaep() {
    use crate::rsa::*;

    let der = include_bytes!("../high/rsa/rsa2048.pkcs8.der");
    let key = DecryptingKey::from_pkcs8(&OAEP_SHA256, der).unwrap();
    let ciphertext = key.public_key().encrypt(&[1; 40], b"").unwrap();
    checked(|| {
        let key = DecryptingKey::from_pkcs8(&OAEP_SHA256, der).unwrap();
        black_box(key.decrypt(ciphertext.as_ref(), b"").is_ok());
    });
}

// Not on aarch64, where BINSEC cannot finish it in a scheduled run's time.
#[cfg(not(rind_backend = "aarch64"))]
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mldsa() {
    use crate::ml_dsa::*;

    fn sign<P: ParameterSet>() {
        let key = KeyPair::<P>::from_seed(&secret::<32>(1)).unwrap();
        black_box(key.sign(&[2; 40]).is_ok());
    }

    checked(|| {
        sign::<MlDsa44>();
        sign::<MlDsa65>();
        sign::<MlDsa87>();
    });
}
