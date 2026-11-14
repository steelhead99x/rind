//! Verification that, under the `wipe` feature, every value owning a secret
//! (a key, keyed state, or a shared secret) is zeroed on drop.
//!
//! Some of this is subject to whims of the compiler, and
//! hand-written drop impls, so we test it here.
//!
//! Is this test sound? Well, it's a deliberate use-after-drop,
//! so no.
//!
//! To make this work deterministically, we depend on two things:
//!  1. The test checks for zeroisation after dropping
//!     a value but before deallocating it. See the function
//!     `check_zeroed_on_drop` for details.
//!  2. The types whose zeroization is being tested must be
//!     _completely_ filled with zero bytes upon drop, including
//!     any padding bytes. If you have a type like this:
//!     ```
//!     #[repr(C)]
//!     struct Key {
//!         a: u8,
//!         // Note: 7 bytes of padding here, due to the "repr(C)"
//!         b: u64,
//!     }
//!     ```
//!     its drop function can't just do a field-wise zeroing
//!     ```
//!     self.a = 0;
//!     self.b = 0;
//!     ```
//!     because this test will check that the padding bytes between
//!     `a` and `b` have been zeroised too.
//!     Similarly, if the object is an enum wrapping different sized
//!     types, like this:
//!     ```
//!     enum Key {
//!         Key128([u8; 16]),
//!         Key256([u8; 32]),
//!     }
//!     ```
//!     this test will check that all `mem::size_of<Key>` bytes have
//!     been zeroised upon drop, even if the value was a `Key::Key128`
//!     that only initialized half of that space.

#![cfg(feature = "wipe")]

use core::mem::size_of;
use core::ops::Deref;
use core::pin::Pin;
use core::ptr;
use std::alloc::{Layout, dealloc};

#[test]
fn rsa() {
    use rind::signature::RsaKeyPair;
    let rsa = RsaKeyPair::from_pkcs1(include_bytes!("../src/high/rsa/rsa8192.der")).unwrap();
    check_zeroed_on_drop(Box::pin(rsa.to_pkcs8()));
    check_zeroed_on_drop(Box::pin(rsa));
}

#[test]
fn rsa_oaep() {
    use rind::rsa::*;
    let key =
        DecryptingKey::from_pkcs1(&OAEP_SHA256, include_bytes!("../src/high/rsa/rsa8192.der"))
            .unwrap();
    check_zeroed_on_drop(Box::pin(key));
}

#[test]
fn blind_rsa() {
    use rind::blind_rsa::*;
    let key = KeyPair::from_pkcs8(
        &RSABSSA_SHA384_PSS_RANDOMIZED,
        include_bytes!("../src/high/rsa/rsa8192.pkcs8.der"),
    )
    .unwrap();
    check_zeroed_on_drop(Box::pin(key));
}

#[test]
fn ecdsa() {
    use rind::signature::{EcdsaKeyPair, sign};
    for (algorithm, pkcs8) in [
        (
            &sign::ECDSA_P256_SHA256_ASN1,
            &include_bytes!("../src/high/ecdsa/secp256r1.pkcs8.der")[..],
        ),
        (
            &sign::ECDSA_P384_SHA384_ASN1,
            &include_bytes!("../src/high/ecdsa/secp384r1.pkcs8.der")[..],
        ),
        (
            &sign::ECDSA_P521_SHA512_ASN1,
            &include_bytes!("../src/high/ecdsa/secp521r1.pkcs8.der")[..],
        ),
    ] {
        let key = EcdsaKeyPair::from_pkcs8(algorithm, pkcs8).unwrap();
        check_zeroed_on_drop(Box::pin(key.to_pkcs8()));
        check_zeroed_on_drop(Box::pin(key.to_scalar()));
        check_zeroed_on_drop(Box::pin(key.to_sec1()));
        check_zeroed_on_drop(Box::pin(key));
    }
}

#[test]
fn ed25519() {
    use rind::signature::Ed25519KeyPair;
    let ed25519 =
        Ed25519KeyPair::from_pkcs8(include_bytes!("../src/high/asn1/testdata/ed25519-p8v2.bin"))
            .unwrap();
    check_zeroed_on_drop(Box::pin(ed25519.to_pkcs8()));
    check_zeroed_on_drop(Box::pin(ed25519.to_pkcs8v1()));
    check_zeroed_on_drop(Box::pin(ed25519.to_seed()));
    let seed = ed25519.to_seed();
    check_zeroed_on_drop(Box::pin(Ed25519KeyPair::from_seed(seed.as_ref()).unwrap()));
    check_zeroed_on_drop(Box::pin(ed25519));
}

#[test]
fn ml_dsa() {
    use rind::signature::sign::{MlDsa44, MlDsa65, MlDsa87, MlDsaKeyPair, MlDsaParameterSet};
    fn check<P: MlDsaParameterSet>() {
        let key = MlDsaKeyPair::<P>::generate().unwrap();
        check_zeroed_on_drop(Box::pin(key.to_pkcs8()));
        check_zeroed_on_drop(Box::pin(key.to_seed().unwrap()));
        let seed = key.to_seed().unwrap();
        check_zeroed_on_drop(Box::pin(
            MlDsaKeyPair::<P>::from_seed(seed.as_ref()).unwrap(),
        ));
        check_zeroed_on_drop(Box::pin(key));
    }
    check::<MlDsa44>();
    check::<MlDsa65>();
    check::<MlDsa87>();
}

#[test]
fn ecdh() {
    use rind::agreement::*;
    for algorithm in [&X25519, &ECDH_P256, &ECDH_P384, &ECDH_P521] {
        let key = PrivateKey::generate(algorithm).unwrap();
        let peer = PrivateKey::generate(algorithm)
            .unwrap()
            .public_key()
            .clone();
        check_zeroed_on_drop(Box::pin(key.agree(peer.as_ref()).unwrap()));
        check_zeroed_on_drop(Box::pin(key.to_scalar()));
        check_zeroed_on_drop(Box::pin(key.to_pkcs8()));
        let loaded = PrivateKey::from_pkcs8(algorithm, key.to_pkcs8().as_ref()).unwrap();
        check_zeroed_on_drop(Box::pin(loaded));
        check_zeroed_on_drop(Box::pin(key));
    }
}

#[test]
fn oprf() {
    use rind::oprf::*;
    for suite in [
        &RISTRETTO255_SHA512,
        &P256_SHA256,
        &P384_SHA384,
        &P521_SHA512,
    ] {
        let key = ServerKey::generate(suite).unwrap();
        let (blind, _) = Blind::new(suite, b"input").unwrap();
        check_zeroed_on_drop(Box::pin(key.evaluate(b"input").unwrap()));
        check_zeroed_on_drop(Box::pin(key.to_bytes()));
        check_zeroed_on_drop(Box::pin(blind));
        check_zeroed_on_drop(Box::pin(key));

        let key = voprf::ServerKey::generate(suite).unwrap();
        let (blind, _) = voprf::Blind::new(suite, b"input").unwrap();
        check_zeroed_on_drop(Box::pin(key.to_bytes()));
        check_zeroed_on_drop(Box::pin(blind));
        check_zeroed_on_drop(Box::pin(key));
    }
}

#[test]
fn vrf() {
    use rind::vrf::*;
    for algorithm in [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI] {
        let key = SecretKey::generate(algorithm).unwrap();
        check_zeroed_on_drop(Box::pin(key.to_bytes()));
        check_zeroed_on_drop(Box::pin(key));
    }
}

#[test]
fn mlkem768() {
    use rind::kem::*;
    let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
    let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
    check_zeroed_on_drop(Box::pin(secret));
    let decapsulated = DecapsulationKey::generate(&ML_KEM_768)
        .unwrap()
        .decapsulate(ciphertext.as_ref())
        .unwrap();
    check_zeroed_on_drop(Box::pin(decapsulated));
    check_zeroed_on_drop(Box::pin(key));
}

#[test]
fn frost() {
    use rind::frost::*;
    let mut dealt = ED25519_SHA512.deal(2, 2).unwrap();
    let share = dealt.signing_shares.pop().unwrap();
    let (nonces, _) = SigningNonces::commit(&dealt.signing_shares[0]).unwrap();
    check_zeroed_on_drop(Box::pin(nonces));
    check_zeroed_on_drop(Box::pin(share));
}

#[test]
fn hpke() {
    use rind::hpke::*;
    let suite = Suite {
        kdf: &HKDF_SHA256,
        aead: &AES_128_GCM,
    };
    for kem in [
        &DHKEM_X25519_HKDF_SHA256,
        &DHKEM_P256_HKDF_SHA256,
        &DHKEM_P384_HKDF_SHA384,
        &DHKEM_P521_HKDF_SHA512,
    ] {
        let key = PrivateKey::generate(kem).unwrap();
        let (enc, sender) = Sender::new(suite, &key.public_key(), b"info").unwrap();
        check_zeroed_on_drop(Box::pin(sender));
        check_zeroed_on_drop(Box::pin(
            Recipient::new(suite, &key, enc.as_ref(), b"info").unwrap(),
        ));
        check_zeroed_on_drop(Box::pin(
            Exporter::recipient(&HKDF_SHA512, &key, enc.as_ref(), b"info").unwrap(),
        ));
        check_zeroed_on_drop(Box::pin(PrivateKey::derive(kem, b"ikm").unwrap()));
        check_zeroed_on_drop(Box::pin(key));
    }
}

#[test]
fn hkdf() {
    use rind::hkdf::*;

    let salt = Salt::new(&HKDF_SHA256, b"salt");
    check_zeroed_on_drop(Box::pin(salt.extract(b"ikm").unwrap()));
    check_zeroed_on_drop(Box::pin(salt));
}

#[test]
fn hmac() {
    use rind::hmac::*;

    for algorithm in [&legacy::HMAC_SHA1, &HMAC_SHA256, &HMAC_SHA384, &HMAC_SHA512] {
        let key = Key::new(algorithm, &[0xffu8; 32]);
        // A partial block leaves message bytes buffered beside the keyed states.
        let mut ctx = Context::with_key(&key);
        ctx.update(&[0xffu8; 3]);
        check_zeroed_on_drop(Box::pin(ctx));
        check_zeroed_on_drop(Box::pin(key));
    }
}

#[test]
fn spake2plus() {
    use rind::spake2plus::*;

    let w0 = [0xff; 32];
    let w1 = [0xee; 32];
    check_zeroed_on_drop(Box::pin(ProverSecrets::new(&w0, &w1).unwrap()));
    check_zeroed_on_drop(Box::pin(VerifierRecord::from_w1(&w0, &w1).unwrap()));

    let (share_p, prover) = ProverSecrets::new(&w0, &w1)
        .unwrap()
        .start(&RFC9383, b"context", b"prover", b"verifier")
        .unwrap();
    let (_, _, verifier) = VerifierRecord::from_w1(&w0, &w1)
        .unwrap()
        .start(&RFC9383, b"context", b"prover", b"verifier", &share_p)
        .unwrap();
    check_zeroed_on_drop(Box::pin(prover));
    check_zeroed_on_drop(Box::pin(verifier));

    let (share_p, prover) = ProverSecrets::new(&w0, &w1)
        .unwrap()
        .start(&RFC9383, b"context", b"prover", b"verifier")
        .unwrap();
    let (share_v, confirm_v, _) = VerifierRecord::from_w1(&w0, &w1)
        .unwrap()
        .start(&RFC9383, b"context", b"prover", b"verifier", &share_p)
        .unwrap();
    let (_, key) = prover.finish(&share_v, &confirm_v).unwrap();
    check_zeroed_on_drop(Box::pin(key));
}

#[test]
fn pbkdf2() {
    use rind::pbkdf2::*;

    for algorithm in [
        &legacy::PBKDF2_HMAC_SHA1,
        &PBKDF2_HMAC_SHA256,
        &PBKDF2_HMAC_SHA384,
        &PBKDF2_HMAC_SHA512,
    ] {
        check_zeroed_on_drop(Box::pin(Secret::new(algorithm, b"password")));
    }
}

#[test]
fn aead() {
    use rind::aead::{
        AES_128_GCM, AES_192_GCM, AES_256_GCM, CHACHA20_POLY1305, Key, RandomizedNonceKey,
    };

    for algorithm in [&AES_128_GCM, &AES_192_GCM, &AES_256_GCM, &CHACHA20_POLY1305] {
        let key = Key::new(algorithm, &[0xffu8; 32][..algorithm.key_len()]).unwrap();
        check_zeroed_on_drop(Box::pin(key));
    }
    check_zeroed_on_drop(Box::pin(RandomizedNonceKey::new(&[0xffu8; 32])));

    use rind::aead::gcm::{self, TagLength};
    use rind::cipher;
    for (algorithm, len) in [
        (&cipher::AES_128, 16),
        (&cipher::AES_192, 24),
        (&cipher::AES_256, 32),
    ] {
        let key = &[0xffu8; 32][..len];
        let key = gcm::Key::new(algorithm, key, TagLength::Truncated32).unwrap();
        check_zeroed_on_drop(Box::pin(key));
    }

    use rind::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
    for algorithm in [&AES_128, &AES_256, &CHACHA20] {
        let key = &[0xffu8; 32][..algorithm.key_len()];
        check_zeroed_on_drop(Box::pin(HeaderProtectionKey::new(algorithm, key).unwrap()));
    }
}

#[test]
fn cipher() {
    use rind::cipher::{
        AES_128, AES_192, AES_256, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, ChaCha20,
    };
    for (algorithm, len) in [(&AES_128, 16), (&AES_192, 24), (&AES_256, 32)] {
        let key = &[0xffu8; 32][..len];
        check_zeroed_on_drop(Box::pin(Aes::new(algorithm, key).unwrap()));
        check_zeroed_on_drop(Box::pin(AesCtr::new(algorithm, key, 128).unwrap()));
        check_zeroed_on_drop(Box::pin(AesCbcEncryptingKey::new(algorithm, key).unwrap()));
        check_zeroed_on_drop(Box::pin(AesCbcDecryptingKey::new(algorithm, key).unwrap()));
    }
    check_zeroed_on_drop(Box::pin(ChaCha20::new(&[0xffu8; 32])));
}

#[test]
fn key_wrap() {
    use rind::key_wrap::{AES_128, AES_192, AES_256, AesKek};
    for (algorithm, len) in [(&AES_128, 16), (&AES_192, 24), (&AES_256, 32)] {
        let key = &[0xffu8; 32][..len];
        check_zeroed_on_drop(Box::pin(AesKek::new(algorithm, key).unwrap()));
    }
}

fn check_zeroed_on_drop<T: Unpin>(value: Pin<Box<T>>) {
    let ptr = value.deref() as *const T as *const u8;
    let len = size_of::<T>();
    assert_ne!(len, 0);
    println!("this value is {len} bytes in length");
    let before_drop = read_into_vec(ptr, len);

    // Drop `value` and then read its contents to verify they've been zeroed.
    //
    // Note that we can't just do `drop(value)` and then read the memory where
    // `value` used to be, because of a race condition: if any code in this or
    // any other thread does a heap allocation between the freeing of `value`
    // and the read, that allocation might reuse the same memory where `value`
    // used to live, and those bytes could be overwritten before the read begins.
    //
    // Instead, we unwrap `value`'s `Pin<Box>` to get a raw pointer, call
    // `drop_in_place` on that raw pointer to invoke the object's `Drop`
    // implementation, then make a copy of the memory where `value` used to live,
    // and then finally deallocate the raw pointer to free the memory.

    // SAFETY: After unpinning `value`, we do not do anything that might move it before dropping it.
    let addr = Box::into_raw(unsafe { Pin::into_inner_unchecked(value) });

    // SAFETY: We obtained `addr` by unwrapping a valid `Box<T>`, so it is aligned and non-null.
    unsafe {
        ptr::drop_in_place(addr);
    }
    let after_drop = read_into_vec(ptr, len);
    // SAFETY: We obtained `addr` by unwrapping a valid `Box<T>`, so it is allocated and `T-`aligned.
    unsafe {
        dealloc(addr as *mut u8, Layout::new::<T>());
    }

    for i in 0..len {
        if after_drop[i] != 0x00 {
            println!("before_drop: {before_drop:02x?}");
            println!("after_drop: {after_drop:02x?}");
            panic!(
                "byte {i} (0x{:x?}) was not cleared after drop",
                after_drop[i]
            );
        }
    }
}

fn read_into_vec(ptr: *const u8, len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);

    for i in 0..len {
        // Safety: none
        let byte = unsafe { ptr::read_volatile(ptr.add(i)) };
        out.push(byte);
    }
    out
}
