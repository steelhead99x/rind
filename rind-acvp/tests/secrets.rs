// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The secret outputs of `__acvp` are a wiping buffer, an even modulus is
//! refused, and a decapsulation key that fails its check is not a length error.

use std::alloc::{Layout, dealloc};
use std::mem::size_of;
use std::pin::Pin;

use rind::Error;
use rind::acvp::{self, SecretBuf};

#[test]
fn secret_buf_is_wiped_on_drop() {
    // Same shape as `rind/tests/zeroing.rs`: drop in place, read, then free.
    // The bytes are in the value, so this sees them. A `Vec` would have freed
    // its buffer inside `Drop`.
    for n in [64, 4896] {
        let value = Box::pin(SecretBuf::from_slice(&vec![0xa5; n]));
        let ptr = &*value as *const SecretBuf as *const u8;
        let len = size_of::<SecretBuf>();
        // SAFETY: `ptr` points at the pinned box, which is still alive.
        assert_ne!(unsafe { ptr.read_volatile() }, 0);
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
        assert_eq!(left, 0, "{n} bytes");
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

fn be_bytes(n: u128) -> Vec<u8> {
    n.to_be_bytes().to_vec()
}
