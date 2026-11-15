// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::aarch64::*;

use super::aes::{_aes128_8_blocks, _aes192_8_blocks, _aes256_8_blocks, HwKey, load, store};
use super::vpaes_armv8::VpaesKey;
use crate::low::AesKey;
use crate::low::generic::ctr::{self, Ctr8, Ctr32};

/// XORs AES-CTR keystream into `inout`.
///
/// The counter blocks are `nonce` followed by the big-endian `counter`,
/// `counter + 1`, and so on, wrapping within 32 bits.
pub(crate) fn apply(key: &AesKey, nonce: &[u8; 12], counter: u32, inout: &mut [u8]) {
    match key {
        AesKey::Hw(key) => ctr::by8(key, nonce, counter, inout),
        AesKey::Vpaes(key) => ctr::blocks(key, nonce, counter, inout),
    }
}

#[target_feature(enable = "aes,neon")]
fn _apply_8(key: &HwKey, nonce: &[u8; 12], counter: u32, inout: &mut [u8; 128]) {
    let mut base = [0u8; 16];
    base[..12].copy_from_slice(nonce);
    let base = vreinterpretq_u32_u8(load(&base));
    // lane 3 holds bytes 12..16 little-endian, so swap to store big-endian
    let block = |i: u32| {
        vreinterpretq_u8_u32(vsetq_lane_u32::<3>(
            counter.wrapping_add(i).swap_bytes(),
            base,
        ))
    };

    let (b0, b1, b2, b3, b4, b5, b6, b7) = encrypt_8(
        key,
        block(0),
        block(1),
        block(2),
        block(3),
        block(4),
        block(5),
        block(6),
        block(7),
    );

    let (blocks, _) = inout.as_chunks_mut::<16>();
    blocks[0] = store(veorq_u8(b0, load(&blocks[0])));
    blocks[1] = store(veorq_u8(b1, load(&blocks[1])));
    blocks[2] = store(veorq_u8(b2, load(&blocks[2])));
    blocks[3] = store(veorq_u8(b3, load(&blocks[3])));
    blocks[4] = store(veorq_u8(b4, load(&blocks[4])));
    blocks[5] = store(veorq_u8(b5, load(&blocks[5])));
    blocks[6] = store(veorq_u8(b6, load(&blocks[6])));
    blocks[7] = store(veorq_u8(b7, load(&blocks[7])));
}

/// Eight blocks under `key`.
#[allow(clippy::too_many_arguments)]
#[inline]
#[target_feature(enable = "aes,neon")]
fn encrypt_8(
    key: &HwKey,
    b0: uint8x16_t,
    b1: uint8x16_t,
    b2: uint8x16_t,
    b3: uint8x16_t,
    b4: uint8x16_t,
    b5: uint8x16_t,
    b6: uint8x16_t,
    b7: uint8x16_t,
) -> (
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
) {
    match key {
        HwKey::Aes128(a128) => _aes128_8_blocks(a128.round_keys(), b0, b1, b2, b3, b4, b5, b6, b7),
        HwKey::Aes192(a192) => _aes192_8_blocks(a192.round_keys(), b0, b1, b2, b3, b4, b5, b6, b7),
        HwKey::Aes256(a256) => _aes256_8_blocks(a256.round_keys(), b0, b1, b2, b3, b4, b5, b6, b7),
    }
}

impl Ctr8 for HwKey {
    fn ctr8(&self, nonce: &[u8; 12], counter: u32, chunk: &mut [u8; 128]) {
        // SAFETY: only a `HaveCryptoExt` token builds `HwKey`, and rind
        // requires NEON.
        unsafe { _apply_8(self, nonce, counter, chunk) }
    }
}

impl Ctr32 for VpaesKey {
    fn ctr32(&self, ivec: &[u8; 16], blocks: &mut [[u8; 16]]) {
        Self::ctr32(self, ivec, blocks)
    }
}
