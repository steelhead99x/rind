// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function G (RFC 9106, section 3.5), in portable
//! Rust.
//!
//! Written from RFC 9106. Every operation is an add, multiply, xor, or
//! rotate on 64-bit words at fixed positions, so it runs in constant time
//! wherever 32-by-32-bit multiplication does.

/// One 1 KiB block of Argon2's memory, as 128 little-endian words.
#[derive(Clone)]
#[repr(C, align(64))]
pub(crate) struct Argon2Block(pub(crate) [u64; 128]);

impl Argon2Block {
    pub(crate) const ZERO: Self = Self([0; 128]);
}

impl crate::low::Zeroable for Argon2Block {}

/// Sets `out` to G(`x`, `y`), or xors G(`x`, `y`) into it when `xor` is set,
/// as passes after the first do.
#[inline(always)]
// Unused on aarch64, where the NEON fill runs.
// The tests still compare that fill to this one.
#[cfg_attr(all(not(test), target_arch = "aarch64"), allow(dead_code))]
pub(crate) fn argon2_compress(x: &Argon2Block, y: &Argon2Block, out: &mut Argon2Block, xor: bool) {
    let mut r = Argon2Block::ZERO;
    for i in 0..128 {
        r.0[i] = x.0[i] ^ y.0[i];
    }
    let mut q = r.clone();

    // P over each row of sixteen consecutive words, then over each column of
    // eight pairs of words, a row's length apart.
    for row in 0..8 {
        permute(&mut q, |v| 16 * row + v);
    }
    for column in 0..8 {
        permute(&mut q, |v| 2 * column + (v & 1) + (v / 2) * 16);
    }

    if xor {
        for i in 0..128 {
            out.0[i] ^= q.0[i] ^ r.0[i];
        }
    } else {
        for i in 0..128 {
            out.0[i] = q.0[i] ^ r.0[i];
        }
    }
}

// RFC 9106's P, over the sixteen words of `block` that `at` maps 0 through
// 15 to.
#[inline(always)]
#[cfg_attr(all(not(test), target_arch = "aarch64"), allow(dead_code))]
fn permute(block: &mut Argon2Block, at: impl Fn(usize) -> usize) {
    let words = &mut block.0;
    let mut v = [0u64; 16];
    for (i, v) in v.iter_mut().enumerate() {
        *v = words[at(i)];
    }
    gb(&mut v, 0, 4, 8, 12);
    gb(&mut v, 1, 5, 9, 13);
    gb(&mut v, 2, 6, 10, 14);
    gb(&mut v, 3, 7, 11, 15);
    gb(&mut v, 0, 5, 10, 15);
    gb(&mut v, 1, 6, 11, 12);
    gb(&mut v, 2, 7, 8, 13);
    gb(&mut v, 3, 4, 9, 14);
    for (i, v) in v.iter().enumerate() {
        words[at(i)] = *v;
    }
}

// RFC 9106's GB: BLAKE2b's G with each addition `a + b` replaced by
// `a + b + 2 * lo(a) * lo(b)`, and no message words.
#[inline(always)]
#[cfg_attr(all(not(test), target_arch = "aarch64"), allow(dead_code))]
fn gb(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize) {
    v[a] = fbla(v[a], v[b]);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = fbla(v[c], v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = fbla(v[a], v[b]);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = fbla(v[c], v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

#[inline(always)]
#[cfg_attr(all(not(test), target_arch = "aarch64"), allow(dead_code))]
fn fbla(x: u64, y: u64) -> u64 {
    let product = (x as u32 as u64) * (y as u32 as u64);
    x.wrapping_add(y).wrapping_add(product.wrapping_mul(2))
}

/// Compares `compress` to the portable permutation on sixty-four blocks
/// and both XOR modes.
#[cfg(test)]
pub(crate) fn assert_matches_portable(
    compress: impl Fn(&Argon2Block, &Argon2Block, &mut Argon2Block, bool),
) {
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    for _ in 0..64 {
        seed = seed
            .wrapping_mul(0x6C62_272E_07BB_0142)
            .wrapping_add(0x9E37);
        let mut x = Argon2Block::ZERO;
        let mut y = Argon2Block::ZERO;
        let mut old = Argon2Block::ZERO;
        for i in 0..128 {
            x.0[i] = (i as u64).wrapping_mul(seed);
            y.0[i] = (i as u64).wrapping_mul(seed ^ 0x1234_5678_9ABC_DEF0) ^ 0x00FF;
            old.0[i] = 0xFFFF_0000_FFFF_0000 ^ seed.wrapping_add(i as u64);
        }
        for xor in [false, true] {
            let (mut ours, mut theirs) = (old.clone(), old.clone());
            compress(&x, &y, &mut ours, xor);
            argon2_compress(&x, &y, &mut theirs, xor);
            assert_eq!(ours.0, theirs.0, "seed={seed:#x} xor={xor}");
        }
    }
}
