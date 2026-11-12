// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Constant-time checks for each secret path through the C ABI, run under
//! valgrind by `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design, and every
//! status, are marked defined before the test checks them. rind itself marks
//! the private keys it generates or parses, so a key's DER encoding, whose
//! structure is public, goes in unmarked.

// Each unsafe block calls the C ABI with live buffers and handles.
#![allow(clippy::undocumented_unsafe_blocks)]

use core::ptr;

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};

use super::*;

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

/// Checks a call's status, which is public, and returns it.
fn ok(status: isize) -> usize {
    public(&status);
    assert!(status >= 0, "status {status}");
    status as usize
}

/// Runs a constructor that stores a handle, and returns the handle.
fn new<T>(f: impl FnOnce(*mut *mut T) -> isize) -> *mut T {
    let mut handle = ptr::null_mut();
    ok(f(&mut handle));
    public(&handle);
    handle
}

/// Calls `f` with a buffer, and returns what it wrote, marked public.
fn out(f: impl FnOnce(*mut u8, usize) -> isize) -> Vec<u8> {
    let mut buf = vec![0; 8192];
    let len = ok(f(buf.as_mut_ptr(), buf.len()));
    buf.truncate(len);
    public(&buf[..]);
    buf
}

#[test]
fn symmetric() {
    for algorithm in 0..4 {
        let key = [7u8; 32];
        let key = &key[..[16, 24, 32, 32][algorithm as usize]];
        secret(key);
        let nonce = [1u8; 12];
        let mut in_out = *b"hello, world\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0";
        secret(&in_out[..12]);
        unsafe {
            let handle = new(|out| rind_dart_aead_key_new(algorithm, key.as_ptr(), key.len(), out));
            ok(rind_dart_aead_seal(
                handle,
                nonce.as_ptr(),
                12,
                b"aad".as_ptr(),
                3,
                in_out.as_mut_ptr(),
                in_out.len(),
            ));
            public(&in_out);
            let len = ok(rind_dart_aead_open(
                handle,
                nonce.as_ptr(),
                12,
                b"aad".as_ptr(),
                3,
                in_out.as_mut_ptr(),
                in_out.len(),
            ));
            public(&in_out);
            assert_eq!(&in_out[..len], b"hello, world");
            rind_dart_aead_key_free(handle);
        }
    }

    let key = [7u8; 32];
    secret(&key);
    let mut in_out = [9u8; 21];
    secret(&in_out[..5]);
    let mut nonce = [0u8; 24];
    unsafe {
        let handle = new(|out| rind_dart_randomized_nonce_key_new(key.as_ptr(), 32, out));
        ok(rind_dart_randomized_nonce_key_seal(
            handle,
            ptr::null(),
            0,
            in_out.as_mut_ptr(),
            in_out.len(),
            nonce.as_mut_ptr(),
        ));
        public(&in_out);
        let len = ok(rind_dart_randomized_nonce_key_open(
            handle,
            nonce.as_ptr(),
            24,
            ptr::null(),
            0,
            in_out.as_mut_ptr(),
            in_out.len(),
        ));
        public(&in_out);
        assert_eq!(in_out[..len], [9; 5]);

        let nonce = [4u8; 24];
        in_out[..5].copy_from_slice(&[9; 5]);
        secret(&in_out[..5]);
        ok(rind_dart_randomized_nonce_key_seal_with_nonce(
            handle,
            nonce.as_ptr(),
            24,
            ptr::null(),
            0,
            in_out.as_mut_ptr(),
            in_out.len(),
        ));
        public(&in_out);
        let len = ok(rind_dart_randomized_nonce_key_open(
            handle,
            nonce.as_ptr(),
            24,
            ptr::null(),
            0,
            in_out.as_mut_ptr(),
            in_out.len(),
        ));
        public(&in_out);
        assert_eq!(in_out[..len], [9; 5]);
        rind_dart_randomized_nonce_key_free(handle);
    }

    let key = [8u8; 32];
    secret(&key);
    let iv = [2u8; 16];
    let mut block = [3u8; 16];
    secret(&block);
    unsafe {
        ok(rind_dart_aes_cbc(
            0,
            key.as_ptr(),
            32,
            iv.as_ptr(),
            16,
            block.as_mut_ptr(),
            block.len(),
        ));
        public(&block);
        ok(rind_dart_aes_cbc(
            1,
            key.as_ptr(),
            32,
            iv.as_ptr(),
            16,
            block.as_mut_ptr(),
            block.len(),
        ));
        public(&block);
        assert_eq!(block, [3; 16]);

        let counter = [1u8; 16];
        let mut stream = *b"ctr-message!!";
        secret(&stream);
        ok(rind_dart_aes_ctr(
            key.as_ptr(),
            32,
            64,
            counter.as_ptr(),
            16,
            stream.as_mut_ptr(),
            stream.len(),
        ));
        public(&stream);
        ok(rind_dart_aes_ctr(
            key.as_ptr(),
            32,
            64,
            counter.as_ptr(),
            16,
            stream.as_mut_ptr(),
            stream.len(),
        ));
        public(&stream);
        assert_eq!(&stream, b"ctr-message!!");

        let nonce = [6u8; 12];
        let mut stream = *b"chacha";
        secret(&stream);
        ok(rind_dart_chacha20(
            key.as_ptr(),
            32,
            nonce.as_ptr(),
            12,
            0,
            stream.as_mut_ptr(),
            stream.len(),
        ));
        public(&stream);
        ok(rind_dart_chacha20(
            key.as_ptr(),
            32,
            nonce.as_ptr(),
            12,
            0,
            stream.as_mut_ptr(),
            stream.len(),
        ));
        public(&stream);
        assert_eq!(&stream, b"chacha");
    }
}

#[test]
fn macs_and_key_derivation() {
    let key = [3u8; 40];
    secret(&key);
    unsafe {
        let hmac = new(|out| rind_dart_hmac_key_new(0, key.as_ptr(), key.len(), out));
        let tag = out(|o, n| rind_dart_hmac_sign(hmac, b"data".as_ptr(), 4, o, n));
        ok(rind_dart_hmac_verify(
            hmac,
            b"data".as_ptr(),
            4,
            tag.as_ptr(),
            tag.len(),
        ));
        let context = new(|out| rind_dart_hmac_context_new(hmac, out));
        ok(rind_dart_hmac_context_update(context, b"data".as_ptr(), 4));
        assert_eq!(out(|o, n| rind_dart_hmac_context_sign(context, o, n)), tag);
        rind_dart_hmac_key_free(hmac);

        let salt = new(|out| rind_dart_hkdf_salt_new(0, b"salt".as_ptr(), 4, out));
        let prk = new(|out| rind_dart_hkdf_extract(salt, key.as_ptr(), key.len(), out));
        let mut okm = [0u8; 42];
        ok(rind_dart_hkdf_expand(
            prk,
            b"info".as_ptr(),
            4,
            okm.as_mut_ptr(),
            okm.len(),
        ));
        rind_dart_hkdf_prk_free(prk);
        rind_dart_hkdf_salt_free(salt);

        let password = new(|out| rind_dart_pbkdf2_secret_new(0, key.as_ptr(), key.len(), out));
        let derived = out(|o, _| rind_dart_pbkdf2_derive(password, 2, b"salt".as_ptr(), 4, o, 32));
        secret(&derived[..]);
        ok(rind_dart_pbkdf2_verify(
            password,
            2,
            b"salt".as_ptr(),
            4,
            derived.as_ptr(),
            derived.len(),
        ));
        rind_dart_pbkdf2_secret_free(password);
    }

    let other = [3u8; 40];
    secret(&other);
    unsafe {
        ok(rind_dart_constant_time_verify(
            key.as_ptr(),
            40,
            other.as_ptr(),
            40,
        ));
    }
}

#[test]
fn agreement() {
    for algorithm in 0..4 {
        unsafe {
            let alice =
                new(|out| rind_dart_agreement_private_key_new(algorithm, 0, ptr::null(), 0, out));
            let bob =
                new(|out| rind_dart_agreement_private_key_new(algorithm, 0, ptr::null(), 0, out));
            let bob_public = out(|o, n| rind_dart_agreement_private_key_export(bob, 0, o, n));

            // Reloads Alice from her scalar, marked secret, and from her PKCS#8.
            let scalar = out(|o, n| rind_dart_agreement_private_key_export(alice, 2, o, n));
            let pkcs8 = out(|o, n| rind_dart_agreement_private_key_export(alice, 1, o, n));
            secret(&scalar[..]);
            let from_scalar = new(|out| {
                rind_dart_agreement_private_key_new(
                    algorithm,
                    1,
                    scalar.as_ptr(),
                    scalar.len(),
                    out,
                )
            });
            let from_pkcs8 = new(|out| {
                rind_dart_agreement_private_key_new(algorithm, 2, pkcs8.as_ptr(), pkcs8.len(), out)
            });

            let agree = |key| {
                out(|o, n| {
                    rind_dart_agreement_agree(key, bob_public.as_ptr(), bob_public.len(), o, n)
                })
            };
            let secret = agree(alice);
            assert_eq!(agree(from_scalar), secret);
            assert_eq!(agree(from_pkcs8), secret);
            for key in [alice, bob, from_scalar, from_pkcs8] {
                rind_dart_agreement_private_key_free(key);
            }
        }
    }
}

#[test]
fn signatures() {
    unsafe {
        for algorithm in 0..6 {
            let pair = new(|out| {
                rind_dart_ecdsa_key_pair_new(algorithm, 0, ptr::null(), 0, ptr::null(), 0, out)
            });
            let pkcs8 = out(|o, n| rind_dart_ecdsa_key_pair_export(pair, 1, o, n));
            let sec1 = out(|o, n| rind_dart_ecdsa_key_pair_export(pair, 2, o, n));
            out(|o, n| rind_dart_ecdsa_key_pair_export(pair, 3, o, n));
            for (source, der) in [(1, &pkcs8), (2, &sec1)] {
                let reloaded = new(|out| {
                    rind_dart_ecdsa_key_pair_new(
                        algorithm,
                        source,
                        der.as_ptr(),
                        der.len(),
                        ptr::null(),
                        0,
                        out,
                    )
                });
                let signature =
                    out(|o, n| rind_dart_ecdsa_sign(reloaded, b"msg".as_ptr(), 3, o, n));
                let public_key =
                    new(|out| rind_dart_key_pair_public_key(0, reloaded.cast(), 0, out));
                ok(rind_dart_public_key_verify(
                    public_key,
                    b"msg".as_ptr(),
                    3,
                    signature.as_ptr(),
                    signature.len(),
                ));
                rind_dart_public_key_free(public_key);
                rind_dart_ecdsa_key_pair_free(reloaded);
            }
            rind_dart_ecdsa_key_pair_free(pair);
        }

        let seed = [5u8; 32];
        secret(&seed);
        let pair =
            new(|out| rind_dart_ed25519_key_pair_new(2, seed.as_ptr(), 32, ptr::null(), 0, out));
        let signature = out(|o, n| rind_dart_ed25519_sign(pair, b"msg".as_ptr(), 3, o, n));
        let pkcs8 = out(|o, n| rind_dart_ed25519_key_pair_export(pair, 1, o, n));
        let reloaded = new(|out| {
            rind_dart_ed25519_key_pair_new(1, pkcs8.as_ptr(), pkcs8.len(), ptr::null(), 0, out)
        });
        assert_eq!(
            out(|o, n| rind_dart_ed25519_sign(reloaded, b"msg".as_ptr(), 3, o, n)),
            signature
        );
        rind_dart_ed25519_key_pair_free(reloaded);
        rind_dart_ed25519_key_pair_free(pair);

        let pair = new(|out| rind_dart_rsa_key_pair_new(0, 0, ptr::null(), 0, out));
        let pkcs8 = out(|o, n| rind_dart_rsa_key_pair_export(pair, 1, o, n));
        let reloaded =
            new(|out| rind_dart_rsa_key_pair_new(1, 0, pkcs8.as_ptr(), pkcs8.len(), out));
        for algorithm in [0, 3] {
            let signature =
                out(|o, n| rind_dart_rsa_sign(reloaded, algorithm, b"msg".as_ptr(), 3, o, n));
            let public_key =
                new(|out| rind_dart_key_pair_public_key(2, reloaded.cast(), algorithm, out));
            ok(rind_dart_public_key_verify(
                public_key,
                b"msg".as_ptr(),
                3,
                signature.as_ptr(),
                signature.len(),
            ));
            rind_dart_public_key_free(public_key);
        }
        let pss = out(|o, n| rind_dart_rsa_sign_pss(reloaded, 0, 16, b"msg".as_ptr(), 3, o, n));
        let public_key = new(|out| rind_dart_key_pair_public_key(2, reloaded.cast(), 6, out));
        ok(rind_dart_public_key_verify(
            public_key,
            b"msg".as_ptr(),
            3,
            pss.as_ptr(),
            pss.len(),
        ));
        rind_dart_public_key_free(public_key);
        rind_dart_rsa_key_pair_free(reloaded);
        rind_dart_rsa_key_pair_free(pair);
    }
}

#[test]
fn encryption() {
    unsafe {
        let decapsulation = new(|out| rind_dart_decapsulation_key_generate(0, out));
        let public_key = out(|o, n| rind_dart_decapsulation_key_public_key(decapsulation, o, n));
        let encapsulation = new(|out| {
            rind_dart_encapsulation_key_new(0, public_key.as_ptr(), public_key.len(), out)
        });
        let mut ciphertext = [0u8; 1088];
        let mut shared = [0u8; 32];
        ok(rind_dart_encapsulate(
            encapsulation,
            ciphertext.as_mut_ptr(),
            1088,
            shared.as_mut_ptr(),
            32,
        ));
        public(&ciphertext);
        public(&shared);
        assert_eq!(
            out(|o, n| rind_dart_decapsulate(decapsulation, ciphertext.as_ptr(), 1088, o, n)),
            shared
        );
        rind_dart_encapsulation_key_free(encapsulation);
        rind_dart_decapsulation_key_free(decapsulation);

        let decrypting = new(|out| rind_dart_decrypting_key_new(0, 0, 0, ptr::null(), 0, out));
        let pkcs8 = out(|o, n| rind_dart_decrypting_key_export(decrypting, 1, o, n));
        let reloaded =
            new(|out| rind_dart_decrypting_key_new(0, 1, 0, pkcs8.as_ptr(), pkcs8.len(), out));
        let encrypting = new(|out| rind_dart_decrypting_key_public_key(reloaded, out));
        let message = [4u8; 16];
        secret(&message);
        let ciphertext =
            out(|o, n| rind_dart_encrypt(encrypting, message.as_ptr(), 16, ptr::null(), 0, o, n));
        assert_eq!(
            out(|o, n| rind_dart_decrypt(
                reloaded,
                ciphertext.as_ptr(),
                ciphertext.len(),
                ptr::null(),
                0,
                o,
                n
            )),
            [4; 16]
        );
        rind_dart_encrypting_key_free(encrypting);
        rind_dart_decrypting_key_free(reloaded);
        rind_dart_decrypting_key_free(decrypting);
    }
}
