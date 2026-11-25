#![no_main]

//! RFC 3394 and RFC 5649 key wrap against aws-lc's, through aws-lc-sys since
//! aws-lc-rs offers no AES-192 KEK, and RustCrypto's. RustCrypto wraps keys
//! the RFCs refuse, such as an empty one, so it checks only the wraps aws-lc
//! accepts, and every unwrap of a length the RFCs allow.

use ::aes::cipher::KeyInit;
use aes_kw::{AesKw, AesKwp};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::key_wrap::{AES_128, AES_192, AES_256, AesKek, Mode};

mod edit;
mod rustcrypto;

use rustcrypto::rustcrypto_aes;

fuzz_target!(|input: (Operation, edit::Edit)| {
    let (op, edit) = input;
    let (ours, kek, key) = match &op {
        Operation::Aes128 { kek, key } => (&AES_128, &kek[..], key),
        Operation::Aes192 { kek, key } => (&AES_192, &kek[..], key),
        Operation::Aes256 { kek, key } => (&AES_256, &kek[..], key),
    };
    let ours = AesKek::new(ours, kek).unwrap();
    let theirs = Theirs::new(kek);

    // Both wrap the keys RFC 5649 allows, alike, and refuse the rest.
    let mut wrapped = vec![0u8; key.len().next_multiple_of(8) + 8];
    let ours_padded = ours.wrap_key(Mode::Kwp, key, &mut wrapped);
    let theirs_padded = theirs.wrap_padded(key);
    assert_eq!(ours_padded.is_ok(), theirs_padded.is_some());
    if let Some(right) = theirs_padded {
        assert_eq!(wrapped, right);
        let mut independent = vec![0u8; wrapped.len()];
        rustcrypto_aes!(kek, Aes => AesKwp::<Aes>::new_from_slice(kek)
            .unwrap()
            .wrap_key(key, &mut independent)
            .unwrap());
        assert_eq!(wrapped, independent);

        // Both unwrap the wrapped key tampered with alike, and refuse it if
        // it changed.
        let changed = edit.apply(&mut wrapped);
        let mut ours_key = vec![0u8; wrapped.len().saturating_sub(8)];
        let ours_result = ours
            .unwrap_key(Mode::Kwp, &wrapped, &mut ours_key)
            .map(|k| k.to_vec());
        assert_eq!(
            ours_result.as_ref().ok(),
            theirs.unwrap_padded(&wrapped).as_ref()
        );
        assert_eq!(ours_result.is_err(), changed);
        // The integrity check fixes the verdict, so RustCrypto must reach
        // it too, but for the one-block input RFC 5649 refuses and
        // RustCrypto unwraps to an empty key.
        if wrapped.len() >= 16 {
            let mut independent = vec![0u8; wrapped.len()];
            let independent = rustcrypto_aes!(kek, Aes => AesKwp::<Aes>::new_from_slice(kek)
                .unwrap()
                .unwrap_key(&wrapped, &mut independent)
                .ok()
                .map(<[u8]>::to_vec));
            assert_eq!(independent.as_ref(), ours_result.as_ref().ok());
        }
    }

    // Both wrap the keys RFC 3394 allows, alike, and refuse the rest.
    let mut wrapped = vec![0u8; key.len() + 8];
    let ours_result = ours.wrap_key(Mode::Kw, key, &mut wrapped);
    let theirs_result = theirs.wrap(key);
    assert_eq!(ours_result.is_ok(), theirs_result.is_some());
    if ours_result.is_err() {
        return;
    }
    assert_eq!(Some(&wrapped), theirs_result.as_ref());
    let mut independent = vec![0u8; key.len() + 8];
    rustcrypto_aes!(kek, Aes => AesKw::<Aes>::new_from_slice(kek)
        .unwrap()
        .wrap_key(key, &mut independent)
        .unwrap());
    assert_eq!(wrapped, independent);

    // Both unwrap the wrapped key tampered with alike, and refuse it if it
    // changed.
    let changed = edit.apply(&mut wrapped);
    let mut ours_key = vec![0u8; wrapped.len().saturating_sub(8)];
    let ours_result = ours
        .unwrap_key(Mode::Kw, &wrapped, &mut ours_key)
        .map(|k| k.to_vec());
    assert_eq!(ours_result.as_ref().ok(), theirs.unwrap(&wrapped).as_ref());
    assert_eq!(ours_result.is_err(), changed);
    // As above, but RFC 3394 refuses inputs of fewer than three blocks,
    // which RustCrypto unwraps.
    if wrapped.len() >= 24 {
        let mut independent = vec![0u8; wrapped.len()];
        let independent = rustcrypto_aes!(kek, Aes => AesKw::<Aes>::new_from_slice(kek)
            .unwrap()
            .unwrap_key(&wrapped, &mut independent)
            .ok()
            .map(<[u8]>::to_vec));
        assert_eq!(independent.as_ref(), ours_result.as_ref().ok());
    }
});

#[derive(Arbitrary, Debug)]
enum Operation {
    Aes128 { kek: [u8; 16], key: Vec<u8> },
    Aes192 { kek: [u8; 24], key: Vec<u8> },
    Aes256 { kek: [u8; 32], key: Vec<u8> },
}

/// aws-lc's KEK, expanded to encrypt and to decrypt.
struct Theirs(aws_lc_sys::AES_KEY, aws_lc_sys::AES_KEY);

impl Theirs {
    fn new(kek: &[u8]) -> Self {
        let bits = 8 * kek.len() as u32;
        // SAFETY: `kek` is `bits / 8` readable bytes, and each key a
        // writable `AES_KEY`.
        unsafe {
            let mut keys: Self = core::mem::zeroed();
            assert_eq!(
                aws_lc_sys::AES_set_encrypt_key(kek.as_ptr(), bits, &mut keys.0),
                0
            );
            assert_eq!(
                aws_lc_sys::AES_set_decrypt_key(kek.as_ptr(), bits, &mut keys.1),
                0
            );
            keys
        }
    }

    /// RFC 3394's wrap of `key`, or `None` if aws-lc refuses it.
    fn wrap(&self, key: &[u8]) -> Option<Vec<u8>> {
        let mut out = vec![0; key.len() + 8];
        // SAFETY: `out` is 8 bytes longer than `key`, as the routine writes,
        // and a null IV is RFC 3394's default.
        let n = unsafe {
            aws_lc_sys::AES_wrap_key(
                &self.0,
                core::ptr::null(),
                out.as_mut_ptr(),
                key.as_ptr(),
                key.len(),
            )
        };
        (usize::try_from(n) == Ok(out.len())).then_some(out)
    }

    /// RFC 3394's unwrap of `wrapped`, or `None` if aws-lc refuses it.
    fn unwrap(&self, wrapped: &[u8]) -> Option<Vec<u8>> {
        let mut out = vec![0; wrapped.len().checked_sub(8)?];
        // SAFETY: `out` is 8 bytes shorter than `wrapped`, as the routine
        // writes, and a null IV is RFC 3394's default.
        let n = unsafe {
            aws_lc_sys::AES_unwrap_key(
                &self.1,
                core::ptr::null(),
                out.as_mut_ptr(),
                wrapped.as_ptr(),
                wrapped.len(),
            )
        };
        (usize::try_from(n) == Ok(out.len())).then_some(out)
    }

    /// RFC 5649's padded wrap of `key`, or `None` if aws-lc refuses it.
    fn wrap_padded(&self, key: &[u8]) -> Option<Vec<u8>> {
        let mut out = vec![0; key.len() + 15];
        let mut n = 0;
        // SAFETY: `out` is `out.len()` writable bytes, the most the routine
        // writes.
        let ok = unsafe {
            aws_lc_sys::AES_wrap_key_padded(
                &self.0,
                out.as_mut_ptr(),
                &mut n,
                out.len(),
                key.as_ptr(),
                key.len(),
            )
        };
        out.truncate(n);
        (ok == 1).then_some(out)
    }

    /// RFC 5649's padded unwrap of `wrapped`, or `None` if aws-lc refuses it.
    fn unwrap_padded(&self, wrapped: &[u8]) -> Option<Vec<u8>> {
        let mut out = vec![0; wrapped.len()];
        let mut n = 0;
        // SAFETY: as in `wrap_padded`.
        let ok = unsafe {
            aws_lc_sys::AES_unwrap_key_padded(
                &self.1,
                out.as_mut_ptr(),
                &mut n,
                out.len(),
                wrapped.as_ptr(),
                wrapped.len(),
            )
        };
        out.truncate(n);
        (ok == 1).then_some(out)
    }
}
