// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 compression in internal RAM on ESP-IDF Xtensa.
//!
//! The portable backend otherwise calls HACL*'s unrolled `sha256_update`
//! through libcrux-sha2. That body is about 12 KiB, so on an ESP32-S3 it
//! fills most of the 16 KiB flash instruction cache and an unrelated move of
//! the caller changes its speed. This module is rind's own rolled
//! compression, the same 16-word window as `generic::sha256`: FIPS 180-4
//! §4.1.2's functions and §6.2.2's schedule and rounds, over fixed-size
//! arrays. ESP-IDF collects `.iram1.*` into IRAM, fetched without that
//! cache. The round constants are a separate table: a variable index cannot
//! use Xtensa's PC-relative literal load, and an IRAM instruction address is
//! not a data address, so on this target the table is `.dram1.*`, which
//! ESP-IDF already collects into internal data RAM. No branch or memory
//! index depends on the message or the state. Release builds of every other
//! target leave this module out.

// FIPS 180-4 §4.1.2. Macros, so a round stays in the caller's IRAM section
// instead of calling a helper the linker can place in flash.
macro_rules! ch {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) ^ (!$x & $z)
    };
}

macro_rules! maj {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) ^ ($x & $z) ^ ($y & $z)
    };
}

macro_rules! bsig0 {
    ($x:expr) => {
        $x.rotate_right(2) ^ $x.rotate_right(13) ^ $x.rotate_right(22)
    };
}

macro_rules! bsig1 {
    ($x:expr) => {
        $x.rotate_right(6) ^ $x.rotate_right(11) ^ $x.rotate_right(25)
    };
}

macro_rules! ssig0 {
    ($x:expr) => {
        $x.rotate_right(7) ^ $x.rotate_right(18) ^ ($x >> 3)
    };
}

macro_rules! ssig1 {
    ($x:expr) => {
        $x.rotate_right(17) ^ $x.rotate_right(19) ^ ($x >> 10)
    };
}

// `words[index mod 16]`. The mask is the round counter, not the message.
macro_rules! window {
    ($words:expr, $index:expr) => {{
        // SAFETY: `$index & 15` is in `0..16`, and `$words` has 16 elements.
        unsafe { *$words.get_unchecked($index & 15) }
    }};
}

macro_rules! round_constant {
    ($t:expr) => {{
        // SAFETY: `$t` is a round number in `0..64`, and `K` has one word per round.
        unsafe { *K.get_unchecked($t) }
    }};
}

// One FIPS 180-4 §6.2.2 round. A macro, not a function, so it stays in the
// caller's IRAM section instead of being outlined into flash.
macro_rules! round {
    ($a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $w_t:expr, $t:expr) => {{
        let t1 = $h
            .wrapping_add(bsig1!($e))
            .wrapping_add(ch!($e, $f, $g))
            .wrapping_add(round_constant!($t))
            .wrapping_add($w_t);
        let t2 = bsig0!($a).wrapping_add(maj!($a, $b, $c));
        $h = $g;
        $g = $f;
        $f = $e;
        $e = $d.wrapping_add(t1);
        $d = $c;
        $c = $b;
        $b = $a;
        $a = t1.wrapping_add(t2);
    }};
}

#[inline(never)]
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".iram1.rind_sha256_compress_block")
)]
fn sha256_compress_block(state: &mut [u32; 8], block: &[u8; 64]) {
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    // The message schedule, kept as a 16-word window. The first 16 words are
    // the block; each later word replaces the one sixteen rounds behind it.
    let mut w = [0u32; 16];
    let (be_words, _) = block.as_chunks::<4>();
    for (slot, be) in w.iter_mut().zip(be_words) {
        *slot = u32::from_be_bytes(*be);
    }

    for t in 0..16 {
        round!(a, b, c, d, e, f, g, h, window!(&w, t), t);
    }

    for t in 16..64 {
        // Read the four schedule words before the store: the new word lands
        // on W[t - 16].
        let w_t = ssig1!(window!(&w, t - 2))
            .wrapping_add(window!(&w, t - 7))
            .wrapping_add(ssig0!(window!(&w, t - 15)))
            .wrapping_add(window!(&w, t - 16));
        // SAFETY: `t & 15` is in `0..16`.
        unsafe { *w.get_unchecked_mut(t & 15) = w_t };
        round!(a, b, c, d, e, f, g, h, w_t, t);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

/// Whole-block SHA-256 compression, in IRAM on ESP-IDF Xtensa.
///
/// A short tail, which the caller does not pass, is left unchanged.
#[inline(never)]
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".iram1.rind_sha256_nblocks")
)]
pub(super) fn sha256_update_nblocks(st: &mut [u32; 8], mut blocks: &[u8]) {
    while let Some((block, rest)) = blocks.split_first_chunk::<64>() {
        sha256_compress_block(st, block);
        blocks = rest;
    }
}

// FIPS 180-4 §4.2.2.
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".dram1.rind_sha256_k")
)]
static K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
