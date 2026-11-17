// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20 on HACL*'s verified rounds in `generic::chacha20`, one block at a
//! time, as x86_64 runs it without AVX2.

use crate::low::generic::chacha20;

pub(crate) struct ChaCha20 {
    key: [u32; 8],
    /// The block counter, then the 96-bit nonce.
    counter_nonce: [u32; 4],
}

impl ChaCha20 {
    /// `nonce` is the little-endian block counter followed by the 96-bit nonce.
    pub(crate) fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        Self {
            key: words(key),
            counter_nonce: words(nonce),
        }
    }

    /// XORs the keystream into `buffer`, starting at the current block, then
    /// moves the counter past every block it touched.
    pub(crate) fn cipher(&mut self, buffer: &mut [u8]) {
        chacha20::cipher(&self.key, &self.counter_nonce, buffer);
        self.counter_nonce[0] =
            self.counter_nonce[0].wrapping_add(buffer.len().div_ceil(64) as u32);
    }
}

/// `bytes` as little-endian words.
fn words<const B: usize, const W: usize>(bytes: &[u8; B]) -> [u32; W] {
    const { assert!(B == 4 * W) };
    let mut words = [0; W];
    for (w, b) in words.iter_mut().zip(bytes.as_chunks::<4>().0) {
        *w = u32::from_le_bytes(*b);
    }
    words
}
