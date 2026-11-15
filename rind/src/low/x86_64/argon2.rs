// Ported from the Argon2 reference implementation, Copyright 2015 Daniel
// Dinu, Dmitry Khovratovich, Jean-Philippe Aumasson, and Samuel Neves, under
// CC0-1.0.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on AVX2.
//!
//! A port of the Argon2 reference implementation's `blamka-round-opt.h`,
//! whose layout holds a block's 128 words in 32 vectors
//! of four: one row's step of P is one call on four vectors, and so is two
//! columns', after their words are moved into place. It runs adds,
//! 32-by-32-bit multiplies, xors, shuffles, and blends, none of which take
//! time that depends on their values.

use core::arch::x86_64::*;

use super::super::generic::argon2::{Argon2Block, argon2_compress as portable};
use super::cpu::HaveAvx2;

/// Argon2's compression function, as `low::generic::argon2` defines it.
pub(crate) fn argon2_compress(x: &Argon2Block, y: &Argon2Block, out: &mut Argon2Block, xor: bool) {
    match HaveAvx2::check() {
        // SAFETY: the token proves AVX2
        Some(_) => unsafe { compress_avx2(x, y, out, xor) },
        None => portable(x, y, out, xor),
    }
}

#[target_feature(enable = "avx2")]
fn compress_avx2(x: &Argon2Block, y: &Argon2Block, out: &mut Argon2Block, xor: bool) {
    let load = |block: &Argon2Block, i: usize| {
        // SAFETY: `i` is below 32, so the 32 bytes read lie in the block,
        // whose 64-byte alignment aligns them.
        unsafe { _mm256_load_si256(block.0.as_ptr().cast::<__m256i>().add(i)) }
    };

    let mut state = [_mm256_setzero_si256(); 32];
    let mut r = [_mm256_setzero_si256(); 32];
    for i in 0..32 {
        state[i] = _mm256_xor_si256(load(x, i), load(y, i));
        r[i] = match xor {
            true => _mm256_xor_si256(state[i], load(out, i)),
            false => state[i],
        };
    }

    for i in 0..4 {
        let [a0, b0, c0, d0, a1, b1, c1, d1] = rows(&mut state, 8 * i);
        round_rows([a0, a1, b0, b1, c0, c1, d0, d1]);
    }
    for i in 0..4 {
        let [a0, a1, b0, b1, c0, c1, d0, d1] = columns(&mut state, i);
        round_columns([a0, a1, b0, b1, c0, c1, d0, d1]);
    }

    for i in 0..32 {
        let word = _mm256_xor_si256(state[i], r[i]);
        // SAFETY: as `load`, writing.
        unsafe { _mm256_store_si256(out.0.as_mut_ptr().cast::<__m256i>().add(i), word) };
    }
}

// The eight vectors of two rows, starting at `first`, in place.
fn rows(state: &mut [__m256i; 32], first: usize) -> [&mut __m256i; 8] {
    let rows: &mut [__m256i; 8] = (&mut state[first..first + 8]).try_into().unwrap();
    rows.each_mut()
}

// Columns `2 * i` and `2 * i + 1`: the vector at `i` of each row, in place.
fn columns(state: &mut [__m256i; 32], i: usize) -> [&mut __m256i; 8] {
    let mut picked = state.iter_mut().skip(i).step_by(4);
    core::array::from_fn(|_| picked.next().unwrap())
}

type Vectors<'a> = [&'a mut __m256i; 8];

// P over two rows: GB down their columns, then their diagonals, which
// rotating each row's B, C, and D by one, two, and three words lines up.
#[target_feature(enable = "avx2")]
#[inline]
fn round_rows(v: Vectors<'_>) {
    let [a0, a1, b0, b1, c0, c1, d0, d1] = v;
    gb(a0, b0, c0, d0);
    gb(a1, b1, c1, d1);
    for (b, c, d) in [
        (&mut *b0, &mut *c0, &mut *d0),
        (&mut *b1, &mut *c1, &mut *d1),
    ] {
        *b = _mm256_permute4x64_epi64(*b, 0b00_11_10_01);
        *c = _mm256_permute4x64_epi64(*c, 0b01_00_11_10);
        *d = _mm256_permute4x64_epi64(*d, 0b10_01_00_11);
    }
    gb(a0, b0, c0, d0);
    gb(a1, b1, c1, d1);
    for (b, c, d) in [
        (&mut *b0, &mut *c0, &mut *d0),
        (&mut *b1, &mut *c1, &mut *d1),
    ] {
        *b = _mm256_permute4x64_epi64(*b, 0b10_01_00_11);
        *c = _mm256_permute4x64_epi64(*c, 0b01_00_11_10);
        *d = _mm256_permute4x64_epi64(*d, 0b00_11_10_01);
    }
}

// P over two columns, each of whose pair of words in a row is half a vector.
// The diagonals need words from both vectors of each of B and D, which blends
// gather and a swap of each 128-bit half's words puts in place.
#[target_feature(enable = "avx2")]
#[inline]
fn round_columns(v: Vectors<'_>) {
    let [a0, a1, b0, b1, c0, c1, d0, d1] = v;
    let swap = |x: __m256i| _mm256_permute4x64_epi64(x, 0b10_11_00_01);
    gb(a0, b0, c0, d0);
    gb(a1, b1, c1, d1);
    (*b0, *b1) = (
        swap(_mm256_blend_epi32(*b0, *b1, 0x33)),
        swap(_mm256_blend_epi32(*b0, *b1, 0xcc)),
    );
    core::mem::swap(c0, c1);
    (*d0, *d1) = (
        swap(_mm256_blend_epi32(*d0, *d1, 0xcc)),
        swap(_mm256_blend_epi32(*d0, *d1, 0x33)),
    );
    gb(a0, b0, c0, d0);
    gb(a1, b1, c1, d1);
    (*b0, *b1) = (
        swap(_mm256_blend_epi32(*b0, *b1, 0xcc)),
        swap(_mm256_blend_epi32(*b0, *b1, 0x33)),
    );
    core::mem::swap(c0, c1);
    (*d0, *d1) = (
        swap(_mm256_blend_epi32(*d0, *d1, 0x33)),
        swap(_mm256_blend_epi32(*d0, *d1, 0xcc)),
    );
}

// RFC 9106's GB on each of four lanes.
#[target_feature(enable = "avx2")]
#[inline]
fn gb(a: &mut __m256i, b: &mut __m256i, c: &mut __m256i, d: &mut __m256i) {
    let rotr24 = _mm256_setr_epi8(
        3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10, 3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13,
        14, 15, 8, 9, 10,
    );
    let rotr16 = _mm256_setr_epi8(
        2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9, 2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12,
        13, 14, 15, 8, 9,
    );
    *a = fbla(*a, *b);
    *d = _mm256_shuffle_epi32(_mm256_xor_si256(*d, *a), 0b10_11_00_01);
    *c = fbla(*c, *d);
    *b = _mm256_shuffle_epi8(_mm256_xor_si256(*b, *c), rotr24);
    *a = fbla(*a, *b);
    *d = _mm256_shuffle_epi8(_mm256_xor_si256(*d, *a), rotr16);
    *c = fbla(*c, *d);
    let x = _mm256_xor_si256(*b, *c);
    *b = _mm256_xor_si256(_mm256_srli_epi64(x, 63), _mm256_add_epi64(x, x));
}

#[target_feature(enable = "avx2")]
#[inline]
fn fbla(x: __m256i, y: __m256i) -> __m256i {
    let product = _mm256_mul_epu32(x, y);
    _mm256_add_epi64(_mm256_add_epi64(x, y), _mm256_add_epi64(product, product))
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn matches_portable() {
        let Some(_) = HaveAvx2::check() else { return };
        let mut seed = 1u64;
        let mut block = || {
            let mut b = Argon2Block::ZERO;
            for w in &mut b.0 {
                seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                *w = seed;
            }
            b
        };
        for xor in [false, true] {
            let (x, y, old) = (block(), block(), block());
            let (mut ours, mut theirs) = (old.clone(), old);
            // SAFETY: AVX2 checked above
            unsafe { compress_avx2(&x, &y, &mut ours, xor) };
            portable(&x, &y, &mut theirs, xor);
            assert_eq!(ours.0, theirs.0);
        }
    }
}
