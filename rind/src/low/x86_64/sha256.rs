// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 with the SHA extensions, as Intel's `SHA256RNDS2` sequence
//! computes it. CPUs without those instructions run `generic::sha256`.
//!
//! The instruction sequence is the one Jeffrey Walton published, itself
//! from Intel's SHA extensions paper. Nothing here is that paper's proof:
//! the unit test checks these rounds against `generic::sha256`.

use core::arch::x86_64::*;

use super::cpu::HaveSha256;

/// Two round constants in the low lane and the next two in the high lane,
/// which is the order `SHA256RNDS2` consumes after one shuffle.
macro_rules! k {
    ($high:expr, $low:expr) => {{
        // The constants are the FIPS words packed little-endian into a lane.
        // A lane can exceed `i64::MAX`, so the literal is a `u64` first.
        let high: u64 = $high;
        let low: u64 = $low;
        _mm_set_epi64x(high as i64, low as i64)
    }};
}

/// Two SHA-256 rounds. The instruction reads the low two lanes of `$msg`,
/// then the shuffle brings the high two down for the next pair.
macro_rules! rounds2 {
    ($state0:ident, $state1:ident, $msg:ident) => {
        $state1 = _mm_sha256rnds2_epu32($state1, $state0, $msg);
        $msg = _mm_shuffle_epi32($msg, 0x0E);
        $state0 = _mm_sha256rnds2_epu32($state0, $state1, $msg);
    };
}

/// Compresses `blocks`.
#[inline(never)]
pub(in crate::low) fn sha256_compress_blocks_shaext(
    state: &mut [u32; 8],
    blocks: &[u8],
    _token: HaveSha256,
) {
    assert!(blocks.len().is_multiple_of(64));
    // SAFETY: `_token` proves the `sha`, `ssse3`, and `sse4.1` features.
    unsafe { sha256_ni(state, blocks) }
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
unsafe fn sha256_ni(state: &mut [u32; 8], blocks: &[u8]) {
    // Byte-swap each 32-bit lane of a big-endian block.
    let mask = _mm_set_epi64x(0x0c0d0e0f08090a0b, 0x0405060700010203);

    // SAFETY: `state` is eight words, so each half is a readable 128-bit load.
    let (mut tmp, mut state1) = unsafe {
        (
            _mm_loadu_si128(state.as_ptr().cast()),
            _mm_loadu_si128(state[4..].as_ptr().cast()),
        )
    };
    tmp = _mm_shuffle_epi32(tmp, 0xB1); // CDAB
    state1 = _mm_shuffle_epi32(state1, 0x1B); // EFGH
    let mut state0 = _mm_alignr_epi8(tmp, state1, 8); // ABEF
    state1 = _mm_blend_epi16(state1, tmp, 0xF0); // CDGH

    let (blocks, _) = blocks.as_chunks::<64>();
    for block in blocks {
        let abef = state0;
        let cdgh = state1;

        // SAFETY: `block` is 64 readable bytes.
        let (m0, m1, m2, m3) = unsafe {
            (
                _mm_loadu_si128(block.as_ptr().cast()),
                _mm_loadu_si128(block[16..].as_ptr().cast()),
                _mm_loadu_si128(block[32..].as_ptr().cast()),
                _mm_loadu_si128(block[48..].as_ptr().cast()),
            )
        };
        let mut msg0 = _mm_shuffle_epi8(m0, mask);
        let mut msg1 = _mm_shuffle_epi8(m1, mask);
        let mut msg2 = _mm_shuffle_epi8(m2, mask);
        let mut msg3 = _mm_shuffle_epi8(m3, mask);

        // Rounds 0-3
        let mut msg = _mm_add_epi32(msg0, k!(0xE9B5DBA5B5C0FBCF, 0x71374491428A2F98));
        rounds2!(state0, state1, msg);

        // Rounds 4-7
        msg = _mm_add_epi32(msg1, k!(0xAB1C5ED5923F82A4, 0x59F111F13956C25B));
        rounds2!(state0, state1, msg);
        msg0 = _mm_sha256msg1_epu32(msg0, msg1);

        // Rounds 8-11
        msg = _mm_add_epi32(msg2, k!(0x550C7DC3243185BE, 0x12835B01D807AA98));
        rounds2!(state0, state1, msg);
        msg1 = _mm_sha256msg1_epu32(msg1, msg2);

        // Rounds 12-15
        msg = _mm_add_epi32(msg3, k!(0xC19BF1749BDC06A7, 0x80DEB1FE72BE5D74));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg0 = _mm_add_epi32(msg0, _mm_alignr_epi8(msg3, msg2, 4));
        msg0 = _mm_sha256msg2_epu32(msg0, msg3);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg2 = _mm_sha256msg1_epu32(msg2, msg3);

        // Rounds 16-19
        msg = _mm_add_epi32(msg0, k!(0x240CA1CC0FC19DC6, 0xEFBE4786E49B69C1));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg1 = _mm_add_epi32(msg1, _mm_alignr_epi8(msg0, msg3, 4));
        msg1 = _mm_sha256msg2_epu32(msg1, msg0);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg3 = _mm_sha256msg1_epu32(msg3, msg0);

        // Rounds 20-23
        msg = _mm_add_epi32(msg1, k!(0x76F988DA5CB0A9DC, 0x4A7484AA2DE92C6F));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg2 = _mm_add_epi32(msg2, _mm_alignr_epi8(msg1, msg0, 4));
        msg2 = _mm_sha256msg2_epu32(msg2, msg1);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg0 = _mm_sha256msg1_epu32(msg0, msg1);

        // Rounds 24-27
        msg = _mm_add_epi32(msg2, k!(0xBF597FC7B00327C8, 0xA831C66D983E5152));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg3 = _mm_add_epi32(msg3, _mm_alignr_epi8(msg2, msg1, 4));
        msg3 = _mm_sha256msg2_epu32(msg3, msg2);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg1 = _mm_sha256msg1_epu32(msg1, msg2);

        // Rounds 28-31
        msg = _mm_add_epi32(msg3, k!(0x1429296706CA6351, 0xD5A79147C6E00BF3));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg0 = _mm_add_epi32(msg0, _mm_alignr_epi8(msg3, msg2, 4));
        msg0 = _mm_sha256msg2_epu32(msg0, msg3);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg2 = _mm_sha256msg1_epu32(msg2, msg3);

        // Rounds 32-35
        msg = _mm_add_epi32(msg0, k!(0x53380D134D2C6DFC, 0x2E1B213827B70A85));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg1 = _mm_add_epi32(msg1, _mm_alignr_epi8(msg0, msg3, 4));
        msg1 = _mm_sha256msg2_epu32(msg1, msg0);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg3 = _mm_sha256msg1_epu32(msg3, msg0);

        // Rounds 36-39
        msg = _mm_add_epi32(msg1, k!(0x92722C8581C2C92E, 0x766A0ABB650A7354));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg2 = _mm_add_epi32(msg2, _mm_alignr_epi8(msg1, msg0, 4));
        msg2 = _mm_sha256msg2_epu32(msg2, msg1);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg0 = _mm_sha256msg1_epu32(msg0, msg1);

        // Rounds 40-43
        msg = _mm_add_epi32(msg2, k!(0xC76C51A3C24B8B70, 0xA81A664BA2BFE8A1));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg3 = _mm_add_epi32(msg3, _mm_alignr_epi8(msg2, msg1, 4));
        msg3 = _mm_sha256msg2_epu32(msg3, msg2);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg1 = _mm_sha256msg1_epu32(msg1, msg2);

        // Rounds 44-47
        msg = _mm_add_epi32(msg3, k!(0x106AA070F40E3585, 0xD6990624D192E819));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg0 = _mm_add_epi32(msg0, _mm_alignr_epi8(msg3, msg2, 4));
        msg0 = _mm_sha256msg2_epu32(msg0, msg3);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg2 = _mm_sha256msg1_epu32(msg2, msg3);

        // Rounds 48-51
        msg = _mm_add_epi32(msg0, k!(0x34B0BCB52748774C, 0x1E376C0819A4C116));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg1 = _mm_add_epi32(msg1, _mm_alignr_epi8(msg0, msg3, 4));
        msg1 = _mm_sha256msg2_epu32(msg1, msg0);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
        msg3 = _mm_sha256msg1_epu32(msg3, msg0);

        // Rounds 52-55
        msg = _mm_add_epi32(msg1, k!(0x682E6FF35B9CCA4F, 0x4ED8AA4A391C0CB3));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg2 = _mm_add_epi32(msg2, _mm_alignr_epi8(msg1, msg0, 4));
        msg2 = _mm_sha256msg2_epu32(msg2, msg1);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

        // Rounds 56-59
        msg = _mm_add_epi32(msg2, k!(0x8CC7020884C87814, 0x78A5636F748F82EE));
        state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
        msg3 = _mm_add_epi32(msg3, _mm_alignr_epi8(msg2, msg1, 4));
        msg3 = _mm_sha256msg2_epu32(msg3, msg2);
        msg = _mm_shuffle_epi32(msg, 0x0E);
        state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

        // Rounds 60-63
        msg = _mm_add_epi32(msg3, k!(0xC67178F2BEF9A3F7, 0xA4506CEB90BEFFFA));
        rounds2!(state0, state1, msg);

        state0 = _mm_add_epi32(state0, abef);
        state1 = _mm_add_epi32(state1, cdgh);
    }

    tmp = _mm_shuffle_epi32(state0, 0x1B); // FEBA
    state1 = _mm_shuffle_epi32(state1, 0xB1); // DCHG
    state0 = _mm_blend_epi16(tmp, state1, 0xF0); // DCBA
    state1 = _mm_alignr_epi8(state1, tmp, 8); // HGFE
    // SAFETY: `state` is eight words, so each half is a writable 128-bit store.
    unsafe {
        _mm_storeu_si128(state.as_mut_ptr().cast(), state0);
        _mm_storeu_si128(state[4..].as_mut_ptr().cast(), state1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::low::{ct, generic};

    const START: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    #[test]
    fn shaext_matches_generic() {
        let Some(token) = HaveSha256::check() else {
            return;
        };
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        ct::secret_slice(&blocks);
        for n in 0..=5 {
            let blocks = &blocks[..n * 64];
            let mut wanted = START;
            generic::sha256::sha256_compress_blocks(&mut wanted, blocks);
            let mut got = START;
            sha256_compress_blocks_shaext(&mut got, blocks, token);
            assert_eq!(ct::into_public(got), ct::into_public(wanted), "{n} blocks");
        }
    }
}
