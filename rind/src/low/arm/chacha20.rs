// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20 on armv7. The state words are RFC 8439 §2.3: the constants, the
//! key, the block counter, and the nonce, each little-endian. The keystream
//! is aws-lc's, in `chacha_armv4`. QUIC header protection's lone block skips
//! this setup and runs the rounds in `generic::chacha20`.

use super::chacha_armv4::chacha20_ctr32;
use super::cpu::HaveNeon;

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
    neon: Option<HaveNeon>,
}

impl ChaCha20 {
    /// `nonce` is the little-endian block counter followed by the 96-bit nonce.
    pub(crate) fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        let mut ctx = [0u32; 16];
        let counter = u32::from_le_bytes([nonce[0], nonce[1], nonce[2], nonce[3]]);
        let n = [
            nonce[4], nonce[5], nonce[6], nonce[7], nonce[8], nonce[9], nonce[10], nonce[11],
            nonce[12], nonce[13], nonce[14], nonce[15],
        ];
        chacha20_init(&mut ctx, key, &n, counter);
        Self {
            ctx,
            neon: HaveNeon::check(),
        }
    }

    /// XORs the keystream into `buffer`, starting at the current block, then
    /// moves the counter past every block it touched.
    pub(crate) fn cipher(&mut self, buffer: &mut [u8]) {
        chacha20_ctr32(&self.ctx, buffer, self.neon);
        self.ctx[12] = self.ctx[12].wrapping_add(buffer.len().div_ceil(64) as u32);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 8439 §2.3.2's initial state. Replacing HACL*'s loader dropped the
    // only check of these words; this is that check, with no CPU feature.
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
