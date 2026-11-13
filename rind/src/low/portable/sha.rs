// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 on rind's portable code in `generic`, as armv7 runs it without the
//! crypto extension, and the SHA-2 family on HACL*'s verified
//! `Hacl_Hash_SHA2`, as libcrux-sha2 ships it. HACL*'s SHA-256 took 0.67-0.93
//! of `generic`'s time at 16 KB on x86_64. ARMv6-M takes `generic`'s rolled
//! SHA-512 instead: HACL*'s unrolled one overflows an RP2040's 16 KB XIP
//! cache and ran about 10x slower there. Its SHA-256 is `armv6m` below,
//! eight rounds to a loop, linked in one section with the padding and
//! finish: HACL*'s fully unrolled SHA-256 is 9.9 KB of Thumb code, so its
//! own lines fill both ways of the cache over 1.7 KB of sets, and any other
//! hot code the linker puts there evicts it on every call.

use libcrux_sha2::hacl::sha256_update_nblocks;
#[cfg(not(all(target_arch = "arm", not(target_has_atomic = "ptr"))))]
use libcrux_sha2::hacl::sha512_update_nblocks;

#[cfg(all(target_arch = "arm", not(target_has_atomic = "ptr")))]
pub(crate) use crate::low::generic::sha512::sha512_compress_blocks;

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;

#[cfg(all(target_arch = "arm", not(target_has_atomic = "ptr")))]
pub(crate) use armv6m::sha256_compress_blocks;

/// HACL* takes a 32-bit length, so longer input goes in pieces of whole
/// blocks below it.
const PIECE: usize = 1 << 31;

#[cfg(not(all(target_arch = "arm", not(target_has_atomic = "ptr"))))]
pub(crate) use sha256_compress_blocks_hacl as sha256_compress_blocks;

/// Compresses whole 64-byte `blocks` into `state`, by HACL*.
pub(crate) fn sha256_compress_blocks_hacl(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    for piece in blocks.chunks(PIECE) {
        sha256_update_nblocks(piece.len() as u32, piece, state);
    }
}

/// Compresses `message`, padded and closed by the big-endian bit `length`.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha1_compress_blocks(state, blocks);
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[cfg_attr(not(all(target_arch = "arm", not(target_has_atomic = "ptr"))), inline)]
#[cfg_attr(
    all(target_arch = "arm", not(target_has_atomic = "ptr")),
    unsafe(link_section = ".text.rind_sha256_hot"),
    inline(never)
)]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha256_compress_blocks(&mut h, blocks);
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(&mut h, crate::low::pad(rest, length, &mut last));
    crate::low::sha256_digest(&h)
}

/// Compresses whole 128-byte `blocks` into `state`.
#[cfg(not(all(target_arch = "arm", not(target_has_atomic = "ptr"))))]
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    for piece in blocks.chunks(PIECE) {
        sha512_update_nblocks(piece.len() as u32, piece, state);
    }
}

/// SHA-256 for ARMv6-M (Arm without CAS atomics, in cfg terms), eight
/// rounds to a loop iteration with the working variables renamed rather than
/// moved, and the 64-word schedule expanded first. It and `sha256_finish`
/// link contiguously in `.text.rind_sha256_hot`, about 2.1 KB, so an RP2040's
/// 16 KB two-way XIP cache holds the short-message path whatever the linker
/// puts beside it. Every index is a loop counter or a constant, and there is
/// no branch on the message or state.
#[cfg(any(test, all(target_arch = "arm", not(target_has_atomic = "ptr"))))]
mod armv6m {
    static K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    /// The input length from which HACL*'s SHA-256 takes the blocks.
    const LONG: usize = 2048;

    /// Compresses whole 64-byte `blocks` into `state`: short input here, long
    /// input by HACL*.
    #[cfg_attr(
        all(target_arch = "arm", not(target_has_atomic = "ptr")),
        unsafe(link_section = ".text.rind_sha256_hot"),
        inline(never)
    )]
    pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
        assert!(blocks.len().is_multiple_of(64));
        // From 2 KB on, the per-call misses are a small share and HACL*'s
        // unrolled rounds are faster per block (6.0% at 16 KB on a Pico).
        if blocks.len() >= LONG {
            return super::sha256_compress_blocks_hacl(state, blocks);
        }
        let (blocks, _) = blocks.as_chunks::<64>();
        for block in blocks {
            compress(state, block);
        }
    }

    #[cfg_attr(
        all(target_arch = "arm", not(target_has_atomic = "ptr")),
        unsafe(link_section = ".text.rind_sha256_hot"),
        inline(never)
    )]
    fn compress(state: &mut [u32; 8], block: &[u8; 64]) {
        let mut w = [0u32; 64];
        let (words, _) = block.as_chunks::<4>();
        for (w, word) in w.iter_mut().zip(words) {
            *w = u32::from_be_bytes(*word);
        }
        for t in 16..64 {
            let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
            let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
            w[t] = w[t - 16]
                .wrapping_add(s0)
                .wrapping_add(w[t - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
        // One round, with the eight working variables named in their order
        // this round: `d` and `h` take the new values, and the next round
        // names them one place on.
        macro_rules! round {
            ($a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $kw:expr) => {
                let s1 = $e.rotate_right(6) ^ $e.rotate_right(11) ^ $e.rotate_right(25);
                let ch = ($e & $f) ^ (!$e & $g);
                let t1 = $h.wrapping_add(s1).wrapping_add(ch).wrapping_add($kw);
                let s0 = $a.rotate_right(2) ^ $a.rotate_right(13) ^ $a.rotate_right(22);
                let maj = ($a & $b) ^ ($a & $c) ^ ($b & $c);
                $d = $d.wrapping_add(t1);
                $h = t1.wrapping_add(s0.wrapping_add(maj));
            };
        }
        let (k8, _) = K.as_chunks::<8>();
        let (w8, _) = w.as_chunks::<8>();
        for (k, w) in k8.iter().zip(w8) {
            round!(a, b, c, d, e, f, g, h, k[0].wrapping_add(w[0]));
            round!(h, a, b, c, d, e, f, g, k[1].wrapping_add(w[1]));
            round!(g, h, a, b, c, d, e, f, k[2].wrapping_add(w[2]));
            round!(f, g, h, a, b, c, d, e, k[3].wrapping_add(w[3]));
            round!(e, f, g, h, a, b, c, d, k[4].wrapping_add(w[4]));
            round!(d, e, f, g, h, a, b, c, k[5].wrapping_add(w[5]));
            round!(c, d, e, f, g, h, a, b, k[6].wrapping_add(w[6]));
            round!(b, c, d, e, f, g, h, a, k[7].wrapping_add(w[7]));
        }

        for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *s = s.wrapping_add(v);
        }
    }

    // ARMv6-M's SHA-256 agrees with HACL*'s, which every other portable
    // target takes, on zero to eight blocks of patterned input, and on each
    // side of the length where HACL*'s takes over.
    #[cfg(test)]
    #[test]
    fn matches_hacl() {
        let mut data = [0u8; 64 * 40];
        let mut x = 0x2545_f491u32;
        for b in data.iter_mut() {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            *b = x as u8;
        }
        for n in (0..=8).chain([31, 32, 33, 40]) {
            let blocks = &data[..n * 64];
            let mut want = [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ];
            let mut got = want;
            super::sha256_update_nblocks(blocks.len() as u32, blocks, &mut want);
            sha256_compress_blocks(&mut got, blocks);
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
