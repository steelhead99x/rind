// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Secret outputs are a wiping buffer: an ML-KEM key, an ECDSA scalar, an
//! ECDH shared secret or a derived key. An even modulus is refused, and a
//! decapsulation key that fails its check is not a length error.

use std::alloc::{Layout, dealloc};
use std::mem::size_of;
use std::pin::Pin;

use rind::Error;
use rind::acvp::{self, SecretBuf};
use rind::agreement::{ECDH_P256, PrivateKey};
use rind::signature::sign::ECDSA_P256_SHA256_FIXED;
use rind::signature::{EcdsaKeyPair, Ed25519KeyPair};
use rind_acvp::{Reply, Wrapper};

fn handle(command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    Wrapper::default().handle(command, args)
}

#[test]
fn secret_buf_is_wiped_on_drop() {
    // Same shape as `rind/tests/zeroing.rs`: drop in place, read, then free.
    // The bytes are in the value, so this sees them. A `Vec` would have freed
    // its buffer inside `Drop`.
    for n in [64, 4896, 255 * 64] {
        assert_wiped(Box::new(SecretBuf::from_slice(&vec![0xa5; n])));
    }
}

#[test]
fn decaps_roundtrip() {
    let (ek, dk) = acvp::mlkem768_keygen(&[7u8; 64]).unwrap();
    assert_eq!(dk.as_slice().len(), 2400);
    let (ciphertext, secret) = acvp::mlkem768_encaps(&ek, &[9u8; 32]).unwrap();
    let opened = acvp::mlkem768_decaps(dk.as_slice(), &ciphertext).unwrap();
    assert_eq!(opened.as_slice(), secret.as_slice());
}

#[test]
fn invalid_decapsulation_key_is_rejected() {
    let err = acvp::mlkem768_decaps(&[0x11; 2400], &[0; 1088]).unwrap_err();
    assert!(
        matches!(err, Error::KeyRejected(_)),
        "{err} should be a rejected key"
    );
    assert!(err.to_string().contains("modulus"), "{err}");
    let err = acvp::mlkem768_decaps(&[0x11; 16], &[0; 1088]).unwrap_err();
    assert_eq!(err, Error::WrongLength);
    let err = acvp::mlkem768_decaps(&[0x11; 2400], &[0; 4]).unwrap_err();
    assert_eq!(err, Error::WrongLength);
}

#[test]
fn rsa_modexp_rejects_an_even_modulus_and_widens_a_short_exponent() {
    let modulus = be_bytes(1u128 << 64 | 13);
    let short = acvp::rsa_modexp(&be_bytes(5u128), &[3], &modulus).unwrap();
    let wide = acvp::rsa_modexp(&be_bytes(5u128), &be_bytes(3u128), &modulus).unwrap();
    assert_eq!(short.as_slice(), wide.as_slice());
    assert_eq!(short.as_slice(), be_bytes(125u128).as_slice());
    assert!(acvp::rsa_modexp(&be_bytes(5u128), &[3], &be_bytes(1u128 << 64 | 14)).is_none());
    assert!(acvp::rsa_modexp(&be_bytes(5u128), &[3], &[0; 16]).is_none());

    // 2^(2^64 + 1) mod 13 = 6. Dropping the high word would leave 2^1 = 2.
    let modulus = 13u64.to_be_bytes();
    let wider =
        acvp::rsa_modexp(&2u64.to_be_bytes(), &be_bytes(1u128 << 64 | 1), &modulus).unwrap();
    assert_eq!(wider.as_slice(), &6u64.to_be_bytes());
}

#[test]
fn rsa_modexp_keeps_the_modulus_encoding_width() {
    for len in [9, 1, 7, 8, 16, 17, 1024] {
        let mut modulus = vec![0; len];
        modulus[len - 1] = 13;
        let result = acvp::rsa_modexp(&[2], &[3], &modulus).unwrap();
        let mut expected = vec![0; len];
        expected[len - 1] = 8;
        assert_eq!(result.as_slice(), expected, "modulus width {len}");
    }
}

#[test]
fn rsa_modexp_rejects_overwide_moduli() {
    for len in [4897, 1025] {
        let mut modulus = vec![0; len];
        modulus[len - 1] = 13;
        assert!(acvp::rsa_modexp(&[2], &[3], &modulus).is_none());
    }
}

fn be_bytes(n: u128) -> Vec<u8> {
    n.to_be_bytes().to_vec()
}

#[test]
fn ecdsa_keygen_scalar_is_a_secret() {
    let mut reply = handle("ECDSA/keyGen", &[b"P-256".to_vec()]).unwrap();
    assert!(reply.is_secret(0));
    assert!(!reply.is_secret(1) && !reply.is_secret(2));
    assert_eq!(reply[0].len(), 32);
    let mut point = vec![0x04];
    point.extend_from_slice(&reply[1]);
    point.extend_from_slice(&reply[2]);
    let key = EcdsaKeyPair::from_scalar_and_public_key(&ECDSA_P256_SHA256_FIXED, &reply[0], &point)
        .unwrap();
    assert_eq!(key.public_key().as_ref(), point.as_slice());
    assert_wiped(reply.take_secret(0).unwrap());
}

#[test]
fn ed25519_seed_is_a_secret() {
    let mut reply = handle("EDDSA/ED-25519/keyGen", &[]).unwrap();
    assert!(reply.is_secret(0));
    assert!(!reply.is_secret(1));
    let key = Ed25519KeyPair::from_seed(&reply[0]).unwrap();
    assert_eq!(key.public_key().as_ref(), &reply[1]);
    assert_wiped(reply.take_secret(0).unwrap());
}

#[test]
fn ecdh_shared_secret_is_a_secret() {
    let scalar = [0x02; 32];
    let peer_scalar = [0x03; 32];
    let ours = PrivateKey::from_scalar(&ECDH_P256, &scalar).unwrap();
    let peer = PrivateKey::from_scalar(&ECDH_P256, &peer_scalar).unwrap();
    let point = peer.public_key();
    let encoded = point.as_ref();
    let (x, y) = encoded[1..].split_at(32);
    let mut reply = handle("ECDH/P-256", &[x.to_vec(), y.to_vec(), scalar.to_vec()]).unwrap();
    assert!(!reply.is_secret(0) && !reply.is_secret(1));
    assert!(reply.is_secret(2));
    let shared = ours.agree(encoded).unwrap();
    assert_eq!(&reply[2], shared.as_ref());
    assert_wiped(reply.take_secret(2).unwrap());
}

#[test]
fn derived_keys_are_owned_wiping_replies() {
    for (hash, hash_len) in [
        ("SHA-1", 20),
        ("SHA2-256", 32),
        ("SHA2-384", 48),
        ("SHA2-512", 64),
    ] {
        let key = vec![0x35; 32];
        let salt = vec![0x57; 16];
        let info = b"derived key".to_vec();
        let mut extracted = handle(
            &format!("HKDF/{hash}/extract"),
            &[key.clone(), salt.clone()],
        )
        .unwrap();
        assert!(extracted.is_secret(0));
        assert_eq!(extracted[0].len(), hash_len);
        let prk = extracted[0].to_vec();
        assert_wiped(extracted.take_secret(0).unwrap());
        let len = (255 * hash_len) as u32;
        for (command, args, expected_len) in [
            (
                format!("KDA/HKDF/{hash}"),
                vec![key, salt.clone(), info.clone(), len.to_ne_bytes().to_vec()],
                len as usize,
            ),
            (
                format!("HKDF/{hash}/expand"),
                vec![len.to_ne_bytes().to_vec(), prk, info],
                len as usize,
            ),
            (
                "PBKDF".to_owned(),
                vec![
                    b"password".to_vec(),
                    salt,
                    1u32.to_ne_bytes().to_vec(),
                    hash.as_bytes().to_vec(),
                    112u32.to_ne_bytes().to_vec(),
                ],
                14,
            ),
        ] {
            let mut reply = handle(&command, &args).unwrap();
            assert!(reply.is_secret(0), "{command}");
            assert_eq!(reply[0].len(), expected_len, "{command}");
            assert_wiped(reply.take_secret(0).unwrap());
        }
    }
}

#[test]
fn unwrapped_keys_are_owned_wiping_replies() {
    for (algorithm, sizes) in [
        ("AES-KW", &[16, 512][..]),
        ("AES-KWP", &[1, 7, 9, 511, 512][..]),
    ] {
        for &len in sizes {
            let key = vec![0xa5; len];
            let args = [
                Vec::new(),
                vec![0x57; 16],
                key.clone(),
                Vec::new(),
                Vec::new(),
            ];
            let wrapped = handle(&format!("{algorithm}/seal"), &args).unwrap();
            let mut args = args;
            args[2] = wrapped[0].to_vec();
            let mut opened = handle(&format!("{algorithm}/open"), &args).unwrap();
            assert_eq!(opened[0], [1]);
            assert!(opened.is_secret(1));
            assert_eq!(opened[1], key);
            assert_wiped(opened.take_secret(1).unwrap());
            args[2][0] ^= 1;
            let failed = handle(&format!("{algorithm}/open"), &args).unwrap();
            assert_eq!(failed[0], [0]);
            assert!(failed[1].is_empty());
        }
        for (operation, len) in [("seal", 513), ("open", 521)] {
            let args = [
                Vec::new(),
                vec![0x57; 16],
                vec![0; len],
                Vec::new(),
                Vec::new(),
            ];
            assert!(handle(&format!("{algorithm}/{operation}"), &args).is_err());
        }
    }
}

#[test]
fn taking_a_secret_keeps_its_wiping_allocation() {
    let mut reply = handle("EDDSA/ED-25519/keyGen", &[]).unwrap();
    let address = reply[0].as_ptr();
    let secret = reply.take_secret(0).unwrap();
    assert_eq!(secret.as_slice().as_ptr(), address);
    assert!(reply[0].is_empty());
    assert!(!reply.is_secret(0));
    assert!(reply.take_secret(1).is_none());
    assert_eq!(reply[1].len(), 32);
    assert_wiped(secret);
}

fn assert_wiped(secret: Box<SecretBuf>) {
    let value = Box::into_pin(secret);
    let ptr = &*value as *const SecretBuf as *const u8;
    let len = size_of::<SecretBuf>();
    let mut before = 0usize;
    for i in 0..len {
        // SAFETY: `ptr` points at the pinned box, which is still alive.
        // A secret can start with a zero byte, so the check is the whole value.
        before |= unsafe { ptr.add(i).read_volatile() } as usize;
    }
    assert_ne!(before, 0);
    // SAFETY: the pin is consumed here and nothing moves the value before
    // `drop_in_place`. The read below happens before `dealloc`.
    let addr = Box::into_raw(unsafe { Pin::into_inner_unchecked(value) });
    unsafe { std::ptr::drop_in_place(addr) };
    let mut left = 0usize;
    for i in 0..len {
        // SAFETY: `addr` is still allocated, and `Drop` has run.
        left |= unsafe { ptr.add(i).read_volatile() } as usize;
    }
    // SAFETY: `addr` came from `Box::into_raw` and has not been freed.
    unsafe { dealloc(addr.cast(), Layout::new::<SecretBuf>()) };
    assert_eq!(left, 0);
}
