// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 compression with the SHA-1 instructions where the CPU has them, and
//! `generic::sha1` otherwise.

use core::arch::aarch64::*;

use crate::low::aarch64::cpu::{self, HaveCryptoExt};

pub(crate) fn sha1_compress_blocks(state: &mut [u32; 5], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    match HaveCryptoExt::check() {
        // SAFETY: the token proves the CPU has the `sha2` cpu feature, which
        // covers the SHA1 instructions, and rind requires `neon`.
        Some(_) => unsafe { sha1(state, blocks) },
        None => crate::low::generic::sha1::sha1_compress_blocks(state, blocks),
    }
}

/// Compresses the end of `message`, padded and closed by `length`.
// Out of line, so `Sha1State::finish_with` stays small enough to inline and
// write the digest where its caller keeps it.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    if !blocks.is_empty() {
        sha1_compress_blocks(state, blocks);
    }
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// Four rounds of `$op` over message words `$w0`, binding `$e_next` for the
/// following four.  The long form also computes the message words four
/// groups ahead into `$w0`.
macro_rules! rounds4 {
    ($op:ident, $k:ident, $abcd:ident, $e:ident, $e_next:ident, $w0:ident, $w1:ident, $w2:ident, $w3:ident) => {
        rounds4!($op, $k, $abcd, $e, $e_next, $w0);
        let $w0 = vsha1su1q_u32(vsha1su0q_u32($w0, $w1, $w2), $w3);
    };

    ($op:ident, $k:ident, $abcd:ident, $e:ident, $e_next:ident, $w0:ident) => {
        let wk = vaddq_u32($w0, $k);
        let $e_next = vsha1h_u32(vgetq_lane_u32::<0>($abcd));
        $abcd = $op($abcd, $e, wk);
    };
}

#[target_feature(enable = "neon,sha2")]
fn sha1(state: &mut [u32; 5], blocks: &[u8]) {
    let k0 = vdupq_n_u32(0x5a827999);
    let k1 = vdupq_n_u32(0x6ed9eba1);
    let k2 = vdupq_n_u32(0x8f1bbcdc);
    let k3 = vdupq_n_u32(0xca62c1d6);

    // SAFETY: `state` is 5 words, so the first 4 are readable
    let mut abcd = unsafe { vld1q_u32(state[0..4].as_ptr()) };
    let mut e = state[4];

    let (chunks, _) = blocks.as_chunks::<64>();
    for block in chunks {
        let abcd_prev = abcd;
        let e_prev = e;

        // prefetch next block
        // SAFETY: prefetches don't constitute an access and are not
        // archtecturally visible.
        unsafe { cpu::prefetch_ro(block.as_ptr().add(64)) };

        // SAFETY: `block` is 64 bytes long and readable, via `as_chunks`
        let (msg0, msg1, msg2, msg3) = unsafe {
            (
                vld1q_u32(block[0..].as_ptr().cast()),
                vld1q_u32(block[16..].as_ptr().cast()),
                vld1q_u32(block[32..].as_ptr().cast()),
                vld1q_u32(block[48..].as_ptr().cast()),
            )
        };

        let msg0 = vreinterpretq_u32_u8(vrev32q_u8(vreinterpretq_u8_u32(msg0)));
        let msg1 = vreinterpretq_u32_u8(vrev32q_u8(vreinterpretq_u8_u32(msg1)));
        let msg2 = vreinterpretq_u32_u8(vrev32q_u8(vreinterpretq_u8_u32(msg2)));
        let msg3 = vreinterpretq_u32_u8(vrev32q_u8(vreinterpretq_u8_u32(msg3)));

        let e0 = e;

        // Rounds 0-19
        rounds4!(vsha1cq_u32, k0, abcd, e0, e1, msg0, msg1, msg2, msg3);
        rounds4!(vsha1cq_u32, k0, abcd, e1, e0, msg1, msg2, msg3, msg0);
        rounds4!(vsha1cq_u32, k0, abcd, e0, e1, msg2, msg3, msg0, msg1);
        rounds4!(vsha1cq_u32, k0, abcd, e1, e0, msg3, msg0, msg1, msg2);
        rounds4!(vsha1cq_u32, k0, abcd, e0, e1, msg0, msg1, msg2, msg3);

        // Rounds 20-39
        rounds4!(vsha1pq_u32, k1, abcd, e1, e0, msg1, msg2, msg3, msg0);
        rounds4!(vsha1pq_u32, k1, abcd, e0, e1, msg2, msg3, msg0, msg1);
        rounds4!(vsha1pq_u32, k1, abcd, e1, e0, msg3, msg0, msg1, msg2);
        rounds4!(vsha1pq_u32, k1, abcd, e0, e1, msg0, msg1, msg2, msg3);
        rounds4!(vsha1pq_u32, k1, abcd, e1, e0, msg1, msg2, msg3, msg0);

        // Rounds 40-59
        rounds4!(vsha1mq_u32, k2, abcd, e0, e1, msg2, msg3, msg0, msg1);
        rounds4!(vsha1mq_u32, k2, abcd, e1, e0, msg3, msg0, msg1, msg2);
        rounds4!(vsha1mq_u32, k2, abcd, e0, e1, msg0, msg1, msg2, msg3);
        rounds4!(vsha1mq_u32, k2, abcd, e1, e0, msg1, msg2, msg3, msg0);
        rounds4!(vsha1mq_u32, k2, abcd, e0, e1, msg2, msg3, msg0, msg1);

        // Rounds 60-79: the schedule is complete after W[76..80]
        rounds4!(vsha1pq_u32, k3, abcd, e1, e0, msg3, msg0, msg1, msg2);
        rounds4!(vsha1pq_u32, k3, abcd, e0, e1, msg0);
        rounds4!(vsha1pq_u32, k3, abcd, e1, e0, msg1);
        rounds4!(vsha1pq_u32, k3, abcd, e0, e1, msg2);
        rounds4!(vsha1pq_u32, k3, abcd, e1, e0, msg3);

        abcd = vaddq_u32(abcd, abcd_prev);
        e = e0.wrapping_add(e_prev);
    }

    // SAFETY: `state` is 5 words, so the first 4 are writable
    unsafe { vst1q_u32(state[0..4].as_mut_ptr(), abcd) };
    state[4] = e;
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Every other test sees only the routine the CPU picks, so the SHA-1
    // instructions are checked against `generic::sha1` here.
    #[test]
    fn hw_matches_generic() {
        if HaveCryptoExt::check().is_none() {
            return;
        }
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for n in 1..=5 {
            let blocks = &blocks[..n * 64];
            let mut want = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
            let mut got = want;
            crate::low::generic::sha1::sha1_compress_blocks(&mut want, blocks);
            // SAFETY: `blocks` is `n` blocks, and the CPU has the SHA-1
            // instructions.
            unsafe { sha1(&mut got, blocks) };
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
