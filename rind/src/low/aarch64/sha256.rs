// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 with the Armv8 SHA-256 instructions where the CPU has them, and
//! `generic::sha256` otherwise.
//!
//! The round order is the public-domain sequence Jeffrey Walton published
//! from ARM and mbedTLS. It is not the HOL Light proof of the assembly this
//! replaced: that proof is of bytes rind no longer ships.

use core::arch::aarch64::*;

use super::cpu::HaveCryptoExt;
use crate::low::generic::sha256_k::K;

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    match HaveCryptoExt::check() {
        // SAFETY: the token proves the SHA-256 instructions, and `blocks`
        // is a whole number of blocks.
        Some(token) => unsafe { compress_hw(token, state, blocks) },
        None => crate::low::generic::sha256::sha256_compress_blocks(state, blocks),
    }
}

/// Compresses `blocks` with the SHA-256 instructions.
///
/// # Safety
///
/// The caller holds a `HaveCryptoExt` token, and `blocks` is a whole number
/// of blocks.
#[target_feature(enable = "neon,sha2")]
unsafe fn compress_hw(_: HaveCryptoExt, state: &mut [u32; 8], blocks: &[u8]) {
    // SAFETY: `state` is eight words. Each `vld1q` loads four of them.
    let (mut state0, mut state1) =
        unsafe { (vld1q_u32(state.as_ptr()), vld1q_u32(state.as_ptr().add(4))) };

    let (blocks, _) = blocks.as_chunks::<64>();
    for block in blocks {
        let saved0 = state0;
        let saved1 = state1;

        // SAFETY: `block` is 64 readable bytes.
        let mut msg = unsafe {
            [
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr()))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(16)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(32)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(48)))),
            ]
        };

        macro_rules! kadd {
            ($msg:expr, $off:expr) => {{
                // SAFETY: `K` is 64 words and `$off` is a multiple of four,
                // at most 60, so this loads four constants inside `K`.
                unsafe { vaddq_u32($msg, vld1q_u32(K.as_ptr().add($off))) }
            }};
        }
        let mut tmp0 = kadd!(msg[0], 0);
        let mut tmp1;
        let mut tmp2;

        msg[0] = vsha256su0q_u32(msg[0], msg[1]);
        tmp2 = state0;
        tmp1 = kadd!(msg[1], 4);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);
        msg[0] = vsha256su1q_u32(msg[0], msg[2], msg[3]);

        msg[1] = vsha256su0q_u32(msg[1], msg[2]);
        tmp2 = state0;
        tmp0 = kadd!(msg[2], 8);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);
        msg[1] = vsha256su1q_u32(msg[1], msg[3], msg[0]);

        msg[2] = vsha256su0q_u32(msg[2], msg[3]);
        tmp2 = state0;
        tmp1 = kadd!(msg[3], 12);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);
        msg[2] = vsha256su1q_u32(msg[2], msg[0], msg[1]);

        msg[3] = vsha256su0q_u32(msg[3], msg[0]);
        tmp2 = state0;
        tmp0 = kadd!(msg[0], 16);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);
        msg[3] = vsha256su1q_u32(msg[3], msg[1], msg[2]);

        msg[0] = vsha256su0q_u32(msg[0], msg[1]);
        tmp2 = state0;
        tmp1 = kadd!(msg[1], 20);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);
        msg[0] = vsha256su1q_u32(msg[0], msg[2], msg[3]);

        msg[1] = vsha256su0q_u32(msg[1], msg[2]);
        tmp2 = state0;
        tmp0 = kadd!(msg[2], 24);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);
        msg[1] = vsha256su1q_u32(msg[1], msg[3], msg[0]);

        msg[2] = vsha256su0q_u32(msg[2], msg[3]);
        tmp2 = state0;
        tmp1 = kadd!(msg[3], 28);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);
        msg[2] = vsha256su1q_u32(msg[2], msg[0], msg[1]);

        msg[3] = vsha256su0q_u32(msg[3], msg[0]);
        tmp2 = state0;
        tmp0 = kadd!(msg[0], 32);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);
        msg[3] = vsha256su1q_u32(msg[3], msg[1], msg[2]);

        msg[0] = vsha256su0q_u32(msg[0], msg[1]);
        tmp2 = state0;
        tmp1 = kadd!(msg[1], 36);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);
        msg[0] = vsha256su1q_u32(msg[0], msg[2], msg[3]);

        msg[1] = vsha256su0q_u32(msg[1], msg[2]);
        tmp2 = state0;
        tmp0 = kadd!(msg[2], 40);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);
        msg[1] = vsha256su1q_u32(msg[1], msg[3], msg[0]);

        msg[2] = vsha256su0q_u32(msg[2], msg[3]);
        tmp2 = state0;
        tmp1 = kadd!(msg[3], 44);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);
        msg[2] = vsha256su1q_u32(msg[2], msg[0], msg[1]);

        msg[3] = vsha256su0q_u32(msg[3], msg[0]);
        tmp2 = state0;
        tmp0 = kadd!(msg[0], 48);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);
        msg[3] = vsha256su1q_u32(msg[3], msg[1], msg[2]);

        tmp2 = state0;
        tmp1 = kadd!(msg[1], 52);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);

        tmp2 = state0;
        tmp0 = kadd!(msg[2], 56);
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);

        tmp2 = state0;
        tmp1 = kadd!(msg[3], 60);
        state0 = vsha256hq_u32(state0, state1, tmp0);
        state1 = vsha256h2q_u32(state1, tmp2, tmp0);

        tmp2 = state0;
        state0 = vsha256hq_u32(state0, state1, tmp1);
        state1 = vsha256h2q_u32(state1, tmp2, tmp1);

        state0 = vaddq_u32(state0, saved0);
        state1 = vaddq_u32(state1, saved1);
    }

    // SAFETY: `state` is eight writable words.
    unsafe {
        vst1q_u32(state.as_mut_ptr(), state0);
        vst1q_u32(state.as_mut_ptr().add(4), state1);
    }
}

/// Compresses the end of `message`, padded and closed by `length`.
#[inline(never)]
fn sha256_compress_padded(state: &mut [u32; 8], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    if !blocks.is_empty() {
        sha256_compress_blocks(state, blocks);
    }
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    sha256_compress_padded(&mut h, message, length);
    crate::low::sha256_digest(&h)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn hw_matches_generic() {
        let Some(token) = HaveCryptoExt::check() else {
            return;
        };
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for n in 0..=5 {
            let blocks = &blocks[..n * 64];
            let mut want = [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ];
            let mut got = want;
            crate::low::generic::sha256::sha256_compress_blocks(&mut want, blocks);
            // SAFETY: the token proves the SHA-256 instructions.
            unsafe { compress_hw(token, &mut got, blocks) };
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
