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
        // Eight blocks through verified-garbage's routines and a tail,
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
    use crate::mid::mlkem::{DecapKey, Message};

    // A fixed message, so every run explores the same ciphertext: BINSEC's
    // term building stalls on a few, for as long as it is given, and a random
    // one made that a flaky check. Which ones stall moves with the compiled
    // code, so a change that stalls this one picks another.
    // See UPSTREAM.md, "BINSEC stalls on some ML-KEM ciphertexts".
    let (_, ciphertext) = DecapKey::<P>::keygen_internal(&[1; 64])
        .encapsulation_key()
        .encaps_internal(Message([0x01; 32]));
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

// Each key signs into both encodings: the fixed one, and ASN.1's DER, whose
// length depends on `r` and `s`, so it must encode them only once they are
// public.
fn ecdsa(algorithms: [&'static crate::ecdsa::SigningAlgorithm; 2], pkcs8: &[u8]) {
    use crate::ecdsa::*;

    checked(|| {
        for algorithm in algorithms {
            let key = KeyPair::from_pkcs8(algorithm, pkcs8).unwrap();
            black_box(key.sign(&secret::<40>(1)).is_ok());
        }
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p256() {
    use crate::ecdsa::sign::*;
    ecdsa(
        [&P256_SHA256_FIXED, &P256_SHA256_ASN1],
        include_bytes!("../high/ecdsa/secp256r1.pkcs8.der"),
    );
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p384() {
    use crate::ecdsa::sign::*;
    ecdsa(
        [&P384_SHA384_FIXED, &P384_SHA384_ASN1],
        include_bytes!("../high/ecdsa/secp384r1.pkcs8.der"),
    );
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_ecdsa_p521() {
    use crate::ecdsa::sign::*;
    ecdsa(
        [&P521_SHA512_FIXED, &P521_SHA512_ASN1],
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
// `ct_binsec_mont16` with the narrow schedule forced. On aarch64 this runs
// `bn_mul_mont` on a wide multiplier and s2n-bignum's `bignum_kmul_32_64`,
// `bignum_ksqr_32_64`, and `bignum_emontredc_8n` on a narrow one, so
// `admin/ct-binsec` runs it again with each schedule forced.
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
fn rsa_sign(pkcs8: &[u8], algorithm: &'static crate::rsa::SigningAlgorithm) {
    use crate::rsa::*;

    checked(|| {
        let key = KeyPair::from_pkcs8(pkcs8).unwrap();
        black_box(key.sign(algorithm, &[1; 40]).is_ok());
    });
}

#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa2048_sign() {
    rsa_sign(
        include_bytes!("../high/rsa/rsa2048.pkcs8.der"),
        &crate::rsa::sign::PKCS1_SHA256,
    );
}

// PSS's encoding, from its fresh salt through MGF1 to the masked block,
// on the same private operation.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa2048_pss() {
    rsa_sign(
        include_bytes!("../high/rsa/rsa2048.pkcs8.der"),
        &crate::rsa::sign::PSS_SHA256,
    );
}

// Only x86_64 runs other code at 24 words than at 16.
#[cfg(rind_backend = "x86_64")]
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_rsa3072_sign() {
    rsa_sign(
        include_bytes!("../high/rsa/rsa3072.pkcs8.der"),
        &crate::rsa::sign::PKCS1_SHA256,
    );
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
#[cfg(all(feature = "ml-dsa", not(rind_backend = "aarch64")))]
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

// Both ends of HPKE's base mode on X25519 and P-256: encapsulation,
// decapsulation, the key schedule, a message each way, and an export. It
// seals with ChaCha20-Poly1305, since BINSEC cannot finish aarch64's AES-GCM
// (see `ct_binsec_aes_gcm`), and HPKE runs the same code around either AEAD.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_hpke() {
    use crate::hpke::*;

    let suite = Suite {
        kdf: &HKDF_SHA256,
        aead: &CHACHA20_POLY1305,
    };
    // The recipient's key, which the region loads again as a secret, so that
    // it opens what was sealed to it here.
    const KEY: u8 = 1;
    let mut sent = Vec::new();
    for (kem, len) in [
        (&DHKEM_X25519_HKDF_SHA256, 32),
        (&DHKEM_P256_HKDF_SHA256, 32),
    ] {
        let key = PrivateKey::from_scalar(kem, &vec![KEY; len]).unwrap();
        let (enc, mut sender) = Sender::new(suite, key.public_key(), b"info").unwrap();
        let mut message = [3; MESSAGE].to_vec();
        sender
            .seal_in_place_append_tag(b"aad", &mut message)
            .unwrap();
        sent.push((kem, len, key.public_key().as_ref().to_vec(), enc, message));
    }
    checked(|| {
        for (kem, len, public_key, enc, message) in &sent {
            let mut out = [0; 32];
            let key = PrivateKey::from_scalar(kem, &secret::<32>(KEY)[..*len]).unwrap();
            let mut recipient = Recipient::new(suite, &key, enc.as_ref(), b"info").unwrap();
            black_box(
                recipient
                    .open_in_place(b"aad", &mut message.clone())
                    .is_ok(),
            );
            recipient.export(b"context", &mut out).unwrap();
            let public_key = PublicKey::new(kem, public_key).unwrap();
            let (_, mut sender) = Sender::new(suite, &public_key, b"info").unwrap();
            let mut message = secret::<MESSAGE>(3).to_vec();
            sender
                .seal_in_place_append_tag(b"aad", &mut message)
                .unwrap();
            sender.export(b"context", &mut out).unwrap();
        }
    });
}

// RFC 9497's OPRF on ristretto255: the client holding a secret input and
// blind, and the server its key, evaluating blindly and directly.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_oprf() {
    use crate::oprf::*;

    checked(|| {
        let server = ServerKey::from_scalar(&RISTRETTO255_SHA512, &secret::<32>(1)).unwrap();
        let (blind, blinded) = Blind::new(&RISTRETTO255_SHA512, &secret::<20>(2)).unwrap();
        let evaluated = server.blind_evaluate(blinded.as_ref()).unwrap();
        black_box(blind.finalize(evaluated.as_ref()).is_ok());
        black_box(server.evaluate(&secret::<20>(2)).is_ok());
    });
}

// The VOPRF on P-384, Privacy Pass's, whose server also proves its
// evaluation with a secret nonce.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_voprf() {
    use crate::oprf::*;

    let (_, blinded) = voprf::Blind::new(&P384_SHA384, &[2; 20]).unwrap();
    checked(|| {
        let server = voprf::ServerKey::from_scalar(&P384_SHA384, &secret::<48>(1)).unwrap();
        black_box(server.blind_evaluate(blinded.as_ref()).is_ok());
    });
}

// The VOPRF client's blinding, on its own, as the server's proof is above.
// Only on the portable backend: x86_64's and aarch64's field arithmetic is
// s2n-bignum's, whose `bignum_tomont_p384` of the hashed input BINSEC cannot
// finish in a scheduled run's time (UPSTREAM.md, "BINSEC stalls on
// s2n-bignum's P-384 arithmetic of a hashed value"). The hash to the curve
// around it is the same code on every backend.
#[cfg(rind_backend = "portable")]
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_voprf_client() {
    use crate::oprf::*;

    checked(|| {
        black_box(voprf::Blind::new(&P384_SHA384, &secret::<20>(2)).is_ok());
    });
}

// Both sides of a SPAKE2+ handshake (RFC 9383), from the password's
// scalars to the confirmed keys.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_spake2plus() {
    use crate::spake2plus::*;

    let session = Session {
        context: b"app",
        id_prover: b"client",
        id_verifier: b"server",
    };
    checked(|| {
        let (w0, w1) = (secret::<40>(0x11), secret::<40>(0x22));
        let prover = ProverSecrets::new(&w0, &w1).unwrap();
        let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
        let (share_p, prover) = prover.start(&RFC9383, &session).unwrap();
        let (share_v, confirm_v, verifier) = verifier.start(&RFC9383, &session, &share_p).unwrap();
        let (confirm_p, prover_key) = prover.finish(&share_v, &confirm_v).unwrap();
        black_box(prover_key);
        black_box(verifier.finish(&confirm_p).is_ok());
    });
}

// One FROST signer's rounds (RFC 9591) on Ed25519 and P-256: loading its
// share, committing to nonces, and signing.
#[test]
#[ignore = "admin/ct-binsec runs it under BINSEC"]
fn ct_binsec_frost() {
    use crate::frost::*;

    let dealt = [&ED25519_SHA512, &P256_SHA256].map(|suite| {
        let (shares, commitment) = deal(suite, 2, 2).unwrap();
        let (_, theirs) = SigningNonces::commit(&shares[1]).unwrap();
        let share = shares[0].to_scalar().as_ref().to_vec();
        (*shares[0].identifier(), share, commitment, theirs)
    });
    checked(|| {
        for (identifier, share, commitment, theirs) in &dealt {
            let mut scalar = secret::<32>(0);
            scalar.copy_from_slice(share);
            let share = SigningShare::from_scalar(identifier, &scalar, commitment).unwrap();
            let (nonces, ours) = SigningNonces::commit(&share).unwrap();
            let package =
                SigningPackage::new(commitment.public_key(), &[ours, theirs.clone()], b"hello")
                    .unwrap();
            black_box(nonces.sign(&share, &package).is_ok());
        }
    });
}
