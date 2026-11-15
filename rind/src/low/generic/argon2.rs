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
fn fbla(x: u64, y: u64) -> u64 {
    let product = (x as u32 as u64) * (y as u32 as u64);
    x.wrapping_add(y).wrapping_add(product.wrapping_mul(2))
}
