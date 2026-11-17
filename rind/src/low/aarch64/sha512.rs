// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512 with the Armv8.2 SHA-512 instructions where the CPU has them,
//! and `generic::sha512` otherwise.
//!
//! The round order is the one mbedtls and RustCrypto use for `sha512h` and
//! `sha512su0`. It is not the HOL Light proof of the assembly this replaced:
//! that proof is of bytes rind no longer ships.

use core::arch::aarch64::*;

use super::cpu::HaveSha3;
use crate::low::generic::sha512::K;

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    match HaveSha3::check() {
        // SAFETY: the token proves the SHA-512 instructions, which Rust
        // names `sha3`, and `blocks` is a whole number of blocks.
        Some(token) => unsafe { compress_hw(token, state, blocks) },
        None => crate::low::generic::sha512::sha512_compress_blocks(state, blocks),
    }
}

/// Two SHA-512 rounds. `$hi` and `$lo` are the lanes the instructions write;
/// `$mid` and `$prev` are the other two state vectors, in the order the
/// next pair rotates them into.
macro_rules! pair {
    ($wk:expr, $koff:expr, $hi:ident, $mid:ident, $lo:ident, $prev:ident) => {{
        // SAFETY: `$koff` is an even index below 80, so the load is two
        // round constants inside `K`.
        let initial = unsafe { vaddq_u64($wk, vld1q_u64(K.as_ptr().add($koff))) };
        let sum = vaddq_u64(vextq_u64::<1>(initial, initial), $hi);
        let intermed = vsha512hq_u64(sum, vextq_u64::<1>($mid, $hi), vextq_u64::<1>($lo, $mid));
        $hi = vsha512h2q_u64(intermed, $lo, $prev);
        $lo = vaddq_u64($lo, intermed);
    }};
}

/// Compresses `blocks` with the SHA-512 instructions.
///
/// # Safety
///
/// The caller holds a `HaveSha3` token, and `blocks` is a whole number of
/// blocks.
#[target_feature(enable = "neon,sha3")]
unsafe fn compress_hw(_: HaveSha3, state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `state` is eight words. Each load is two of them.
    let (mut ab, mut cd, mut ef, mut gh) = unsafe {
        (
            vld1q_u64(state.as_ptr()),
            vld1q_u64(state.as_ptr().add(2)),
            vld1q_u64(state.as_ptr().add(4)),
            vld1q_u64(state.as_ptr().add(6)),
        )
    };

    let (blocks, _) = blocks.as_chunks::<128>();
    for block in blocks {
        let ab0 = ab;
        let cd0 = cd;
        let ef0 = ef;
        let gh0 = gh;

        // SAFETY: `block` is 128 readable bytes, and each load is 16 of them.
        let (mut s0, mut s1, mut s2, mut s3, mut s4, mut s5, mut s6, mut s7) = unsafe {
            (
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr()))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(16)))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(32)))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(48)))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(64)))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(80)))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(96)))),
                vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(block.as_ptr().add(112)))),
            )
        };

        pair!(s0, 0, gh, ef, cd, ab);
        pair!(s1, 2, ef, cd, ab, gh);
        pair!(s2, 4, cd, ab, gh, ef);
        pair!(s3, 6, ab, gh, ef, cd);
        pair!(s4, 8, gh, ef, cd, ab);
        pair!(s5, 10, ef, cd, ab, gh);
        pair!(s6, 12, cd, ab, gh, ef);
        pair!(s7, 14, ab, gh, ef, cd);

        let mut t = 16;
        while t < 80 {
            s0 = vsha512su1q_u64(vsha512su0q_u64(s0, s1), s7, vextq_u64::<1>(s4, s5));
            pair!(s0, t, gh, ef, cd, ab);
            s1 = vsha512su1q_u64(vsha512su0q_u64(s1, s2), s0, vextq_u64::<1>(s5, s6));
            pair!(s1, t + 2, ef, cd, ab, gh);
            s2 = vsha512su1q_u64(vsha512su0q_u64(s2, s3), s1, vextq_u64::<1>(s6, s7));
            pair!(s2, t + 4, cd, ab, gh, ef);
            s3 = vsha512su1q_u64(vsha512su0q_u64(s3, s4), s2, vextq_u64::<1>(s7, s0));
            pair!(s3, t + 6, ab, gh, ef, cd);
            s4 = vsha512su1q_u64(vsha512su0q_u64(s4, s5), s3, vextq_u64::<1>(s0, s1));
            pair!(s4, t + 8, gh, ef, cd, ab);
            s5 = vsha512su1q_u64(vsha512su0q_u64(s5, s6), s4, vextq_u64::<1>(s1, s2));
            pair!(s5, t + 10, ef, cd, ab, gh);
            s6 = vsha512su1q_u64(vsha512su0q_u64(s6, s7), s5, vextq_u64::<1>(s2, s3));
            pair!(s6, t + 12, cd, ab, gh, ef);
            s7 = vsha512su1q_u64(vsha512su0q_u64(s7, s0), s6, vextq_u64::<1>(s3, s4));
            pair!(s7, t + 14, ab, gh, ef, cd);
            t += 16;
        }

        ab = vaddq_u64(ab, ab0);
        cd = vaddq_u64(cd, cd0);
        ef = vaddq_u64(ef, ef0);
        gh = vaddq_u64(gh, gh0);
    }

    // SAFETY: `state` is eight writable words.
    unsafe {
        vst1q_u64(state.as_mut_ptr(), ab);
        vst1q_u64(state.as_mut_ptr().add(2), cd);
        vst1q_u64(state.as_mut_ptr().add(4), ef);
        vst1q_u64(state.as_mut_ptr().add(6), gh);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn hw_matches_generic() {
        let Some(token) = HaveSha3::check() else {
            return;
        };
        let blocks: Vec<u8> = (0..5 * 128u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for n in 0..=5 {
            let blocks = &blocks[..n * 128];
            let mut want = [
                0x6a09e667f3bcc908,
                0xbb67ae8584caa73b,
                0x3c6ef372fe94f82b,
                0xa54ff53a5f1d36f1,
                0x510e527fade682d1,
                0x9b05688c2b3e6c1f,
                0x1f83d9abfb41bd6b,
                0x5be0cd19137e2179,
            ];
            let mut got = want;
            crate::low::generic::sha512::sha512_compress_blocks(&mut want, blocks);
            // SAFETY: the token proves the SHA-512 instructions.
            unsafe { compress_hw(token, &mut got, blocks) };
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
