// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20-Poly1305 from separate ChaCha20 and Poly1305 passes, where no
//! one-pass routine runs.

use crate::low::chacha20::ChaCha20;
#[cfg(not(rind_backend = "aarch64"))]
use crate::low::ct_equal;
use crate::low::poly1305::Poly1305;

/// Encrypts `inout` in place, returning the tag over `aad` and the ciphertext.
pub(crate) fn seal(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    cipher(key, nonce, aad, inout, true)
}

/// Decrypts `inout` in place, and returns whether `tag` is its tag over
/// `aad` and the ciphertext, a secret.
// aarch64 tests compare only `seal` with the one-pass routines.
#[cfg(not(rind_backend = "aarch64"))]
pub(crate) fn open(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    ct_equal(&cipher(key, nonce, aad, inout, false), tag)
}

fn cipher(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8], seal: bool) -> [u8; 16] {
    let mut counter_nonce = [0u8; 16];
    counter_nonce[4..].copy_from_slice(nonce);

    // Block 0's first half keys Poly1305.
    let mut chacha = ChaCha20::new(key, &counter_nonce);
    let mut poly_key = [0u8; 32];
    chacha.cipher(&mut poly_key);
    let mut poly = Poly1305::new(&poly_key);

    // AAD || pad(AAD) || ciphertext || pad(ciphertext) || len_64(AAD) || len_64(ciphertext)
    let pad = |poly: &mut Poly1305, len: usize| {
        if !len.is_multiple_of(16) {
            poly.add_bytes(&[0u8; 16][..16 - len % 16]);
        }
    };
    poly.add_bytes(aad);
    pad(&mut poly, aad.len());
    if seal {
        chacha.cipher(inout);
        poly.add_bytes(inout);
    } else {
        poly.add_bytes(inout);
        chacha.cipher(inout);
    }
    pad(&mut poly, inout.len());
    // Both lengths are public, and fill one block, so Poly1305 takes them in
    // one update, with no partial-block buffering.
    let mut lengths = [0u8; 16];
    lengths[..8].copy_from_slice(&(aad.len() as u64).to_le_bytes());
    lengths[8..].copy_from_slice(&(inout.len() as u64).to_le_bytes());
    poly.add_bytes(&lengths);
    poly.finish()
}
