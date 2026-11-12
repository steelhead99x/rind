// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The harnesses `admin/ct-binsec` checks under BINSEC: each runs one
//! primitive's secret paths through the public API in a single checked
//! region. A key is secret from where rind marks it, once parsed, and a
//! harness marks the other secrets it passes, such as a plaintext. A
//! harness ignores what a declassified check returns, since BINSEC takes
//! both of its values.

use core::hint::black_box;

use crate::low::ct;
use crate::low::ct_binsec::checked;

/// `N` bytes of `fill`, marked secret.
fn secret<const N: usize>(fill: u8) -> [u8; N] {
    let bytes = [fill; N];
    ct::secret_slice(&bytes);
    bytes
}

// Messages take a whole block, then a partial one, through each cipher's
// tail handling, at a length that keeps BINSEC's search short.
const MESSAGE: usize = 75;

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
        let tag = key
            .seal_in_place_separate_tag(nonce(), &[4; 21], &mut msg)
            .unwrap();
        black_box(
            key.open_in_place_separate_tag(nonce(), &[4; 21], tag, &mut msg)
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
            encrypting.encrypt(iv, &mut msg);
            let decrypting = AesCbcDecryptingKey::new(algorithm, key).unwrap();
            black_box(decrypting.decrypt(&[3; 16], &mut msg).is_ok());
        }
    });
}

// One block, since BINSEC cannot decode the `vinsertf128` that LLVM emits
// for the AVX2 kernel longer messages take; ctgrind checks that one.
// See UPSTREAM.md, "BINSEC cannot decode much of what rind runs".
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_chacha20() {
    use crate::cipher::*;

    checked(|| {
        let key = ChaCha20::new(&secret(1));
        key.apply_keystream(&[2; 12], 3, &mut secret::<64>(4))
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
            kek.wrap(&secret::<16>(2), &mut wrapped).unwrap();
            black_box(kek.unwrap(&wrapped, &mut key).is_ok());
            let (mut wrapped, mut key) = ([0; 32], [0; 20]);
            kek.wrap_padded(&secret::<20>(2), &mut wrapped).unwrap();
            black_box(kek.unwrap_padded(&wrapped, &mut key).is_ok());
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
        let prk = Salt::new(&HKDF_SHA256, &[1; 32]).extract(&secret::<32>(2));
        let mut okm = [0; 80];
        prk.expand(&[b"info"], okm.len()).fill(&mut okm).unwrap();
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
    use crate::signature::*;

    checked(|| {
        let key = Ed25519KeyPair::from_seed(&[1; 32]).unwrap();
        key.sign(&secret::<40>(2))
    });
}

fn ecdsa(algorithm: &'static crate::signature::EcdsaSigningAlgorithm, pkcs8: &[u8]) {
    use crate::signature::*;

    checked(|| {
        let key = EcdsaKeyPair::from_pkcs8(algorithm, pkcs8).unwrap();
        black_box(key.sign(&secret::<40>(1)).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p256() {
    use crate::signature::sign::ECDSA_P256_SHA256_FIXED;
    ecdsa(
        &ECDSA_P256_SHA256_FIXED,
        include_bytes!("../high/ecdsa/secp256r1.pkcs8.der"),
    );
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p384() {
    use crate::signature::sign::ECDSA_P384_SHA384_FIXED;
    ecdsa(
        &ECDSA_P384_SHA384_FIXED,
        include_bytes!("../high/ecdsa/secp384r1.pkcs8.der"),
    );
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p521() {
    use crate::signature::sign::ECDSA_P521_SHA512_FIXED;
    ecdsa(
        &ECDSA_P521_SHA512_FIXED,
        include_bytes!("../high/ecdsa/secp521r1.pkcs8.der"),
    );
}

// The Montgomery products RSA's private operation runs at its CRT widths,
// 16, 24, and 32 words: s2n-bignum's Karatsuba routines and aws-lc's
// `bn_mul4x_mont` and `bn_sqr8x_mont` on x86_64. BINSEC cannot finish the
// exponentiation that runs thousands of them.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_mont_mul() {
    use crate::low::{mont_mul, mont_sqr};

    checked(|| {
        for k in [16, 24, 32] {
            let (x, mut y, mut z) = ([1u64; 32], [2u64; 32], [0u64; 32]);
            // CRT's modulus is a private prime, and its `-m^-1 mod 2^64`
            // with it; the concrete values are an odd modulus and its 1.
            let m = [u64::MAX; 32];
            ct::secret_slice(&x[..k]);
            ct::secret_slice(&y[..k]);
            ct::secret_slice(&m[..k]);
            let n0 = ct::into_secret(1u64);
            mont_mul(&mut z[..k], &x[..k], &y[..k], &m[..k], n0);
            mont_sqr(&mut y[..k], &z[..k], &m[..k], n0);
            black_box(&y);
        }
    });
}

// The reduction RSA's key check runs on the private exponent, whose loop
// calls `bignum_modadd` where LLVM may inline it, out of `admin/prove
// bytes`'s reach.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_reduce_even() {
    use crate::low::PosInt;

    checked(|| {
        let d = PosInt::<33>::from_words(&[1; 32]).unwrap();
        let p_1 = PosInt::<16>::from_words(&[3; 16]).unwrap();
        ct::secret_slice(d.as_words());
        ct::secret_slice(p_1.as_words());
        black_box(d.reduce_even(&p_1));
    });
}

// RSA's padding check, on a decrypted message: BINSEC cannot finish the
// private operation that decrypts it, at 2048 bits, in a nightly's time.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa_oaep_padding() {
    use crate::high::hash::Sha256;
    use crate::high::pkcs1::{decode_oaep, encode_oaep};
    use crate::mid::rng::SliceRandomSource;

    let mut em = [0; 256];
    encode_oaep::<Sha256>(&mut em, &mut SliceRandomSource(&[2; 32]), &[1; 40], b"").unwrap();
    checked(|| {
        let mut em = em;
        ct::secret_slice(&em);
        let mut out = [0; 256];
        black_box(decode_oaep::<Sha256>(&mut em, b"", &mut out).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_constant_time_verify() {
    black_box(checked(|| {
        crate::constant_time::verify(&secret::<33>(1), &secret::<33>(2)).is_ok()
    }));
}
