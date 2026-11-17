// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20 on armv7. The state words are RFC 8439 §2.3: the constants, the
//! key, the block counter, and the nonce, each little-endian. The keystream
//! is HACL*'s rounds in `generic::chacha20`. QUIC header protection's lone
//! block skips this setup and runs those rounds directly.
//!
//! 32-bit Arm NEON intrinsics are unstable on the toolchain this crate builds
//! with, so this backend does not ship a NEON keystream.

use crate::low::generic::chacha20;

const CONSTANTS: [u32; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

fn chacha20_init(ctx: &mut [u32; 16], key: &[u8; 32], nonce: &[u8; 12], counter: u32) {
    ctx[0..4].copy_from_slice(&CONSTANTS);
    for (i, word) in key.as_chunks::<4>().0.iter().enumerate() {
        ctx[4 + i] = u32::from_le_bytes(*word);
    }
    ctx[12] = counter;
    for (i, word) in nonce.as_chunks::<4>().0.iter().enumerate() {
        ctx[13 + i] = u32::from_le_bytes(*word);
    }
}

pub(crate) struct ChaCha20 {
    ctx: [u32; 16],
}

impl ChaCha20 {
    /// `nonce` is the little-endian block counter followed by the 96-bit nonce.
    pub(crate) fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        let mut ctx = [0u32; 16];
        // `nonce` is 16 bytes: a 32-bit counter, then 12 nonce bytes.
        let counter = u32::from_le_bytes(*nonce.first_chunk::<4>().unwrap());
        let n: &[u8; 12] = nonce.last_chunk::<12>().unwrap();
        chacha20_init(&mut ctx, key, n, counter);
        Self { ctx }
    }

    /// XORs the keystream into `buffer`, starting at the current block, then
    /// moves the counter past every block it touched.
    pub(crate) fn cipher(&mut self, buffer: &mut [u8]) {
        let key: &[u32; 8] = self.ctx[4..12].try_into().unwrap();
        let counter_nonce: &[u32; 4] = self.ctx[12..16].try_into().unwrap();
        chacha20::cipher(key, counter_nonce, buffer);
        self.ctx[12] = self.ctx[12].wrapping_add(buffer.len().div_ceil(64) as u32);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 8439 §2.3.2's initial state.
    #[test]
    fn state_matches_rfc8439() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        // Block counter 1, then the 96-bit nonce 00000009 0000004a 00000000.
        let nonce = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00,
            0x00, 0x00,
        ];
        let state = ChaCha20::new(&key, &nonce);
        assert_eq!(
            state.ctx,
            [
                0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0x03020100, 0x07060504, 0x0b0a0908,
                0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x00000001, 0x09000000,
                0x4a000000, 0x00000000,
            ]
        );
    }
}
