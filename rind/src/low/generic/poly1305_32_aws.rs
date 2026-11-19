// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! aws-lc's Poly1305, for the 26-bit limbs' differential test.
//!
//! This file is the `unsafe` call. The limbs' `debug_assert`s stay in
//! `poly1305_32.rs`, which `low::tests::no_debug_assert_beside_unsafe` keeps
//! apart from `unsafe`.

use aws_lc_sys::{CRYPTO_poly1305_finish, CRYPTO_poly1305_init, CRYPTO_poly1305_update};

/// One tag from `CRYPTO_poly1305_init`, `CRYPTO_poly1305_update`, and
/// `CRYPTO_poly1305_finish` (`include/openssl/poly1305.h`).
/// `poly1305_state` there is `uint8_t[512]`.
pub(crate) fn tag(key: &[u8; 32], msg: &[u8]) -> [u8; 16] {
    let mut state = [0u8; 512];
    let mut mac = [0u8; 16];
    let state_ptr = (&mut state as *mut [u8; 512]).cast::<aws_lc_sys::poly1305_state>();
    // SAFETY: `state` is the 512-byte `poly1305_state`, `key` is 32 bytes,
    // and `msg` is the length passed with it. aws-lc writes 16 tag bytes.
    unsafe {
        CRYPTO_poly1305_init(state_ptr, key.as_ptr());
        CRYPTO_poly1305_update(state_ptr, msg.as_ptr(), msg.len());
        CRYPTO_poly1305_finish(state_ptr, mac.as_mut_ptr());
    }
    mac
}
