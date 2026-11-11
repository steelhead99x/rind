// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on AVX-512.
//!
//! The permutation is the Argon2 reference implementation's AVX-512F
//! `fill_block`, copyright 2015 Daniel Dinu, Dmitry Khovratovich, Jean-Philippe
//! Aumasson, and Samuel Neves, used under Apache-2.0 (also offered as
//! CC0-1.0). It measured faster than the scalar permutation and than
//! RustCrypto's AVX2 one. The lane shuffles are that code's, so a block it
//! returns matches the scalar one.

use core::arch::x86_64::*;

use super::cpu::HaveAvx512F;
use crate::low::argon2::{Block, compress as compress_scalar};

/// `G(prev, reference)`, the AVX-512 permutation when the CPU has it.
pub(crate) fn compress(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    if HaveAvx512F::check().is_some() {
        // SAFETY: `HaveAvx512F` is proof of AVX-512F, and the blocks are 1024
        // bytes each, which the loads and stores stay inside.
        unsafe { compress_avx512(next, prev, reference, with_xor) };
    } else {
        compress_scalar(next, prev, reference, with_xor);
    }
}

#[target_feature(enable = "avx512f")]
unsafe fn compress_avx512(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    // SAFETY: `prev` is 1024 bytes, as `load` requires.
    let mut state = unsafe { load(prev) };
    let mut xy = [_mm512_setzero_si512(); 16];
    // SAFETY: each block is 1024 aligned bytes, sixteen 64-byte lanes.
    unsafe {
        for i in 0..16 {
            let r = _mm512_loadu_si512(reference.0.as_ptr().add(i * 8).cast());
            state[i] = _mm512_xor_si512(state[i], r);
            xy[i] = if with_xor {
                let n = _mm512_loadu_si512(next.0.as_ptr().add(i * 8).cast());
                _mm512_xor_si512(state[i], n)
            } else {
                state[i]
            };
        }
        for i in 0..2 {
            round1(&mut state, i);
        }
        for i in 0..2 {
            round2(&mut state, i);
        }
        for i in 0..16 {
            state[i] = _mm512_xor_si512(state[i], xy[i]);
            _mm512_storeu_si512(next.0.as_mut_ptr().add(i * 8).cast(), state[i]);
        }
    }
}

#[target_feature(enable = "avx512f")]
unsafe fn load(block: &Block) -> [__m512i; 16] {
    let mut state = [_mm512_setzero_si512(); 16];
    // SAFETY: `block` is 1024 bytes.
    unsafe {
        for (i, lane) in state.iter_mut().enumerate() {
            *lane = _mm512_loadu_si512(block.0.as_ptr().add(i * 8).cast());
        }
    }
    state
}

// `_MM_SHUFFLE` as the C headers spell it.
const fn shuffle(z: i32, y: i32, x: i32, w: i32) -> i32 {
    (z << 6) | (y << 4) | (x << 2) | w
}

#[target_feature(enable = "avx512f")]
fn muladd(x: __m512i, y: __m512i) -> __m512i {
    let z = _mm512_mul_epu32(x, y);
    _mm512_add_epi64(_mm512_add_epi64(x, y), _mm512_add_epi64(z, z))
}

#[target_feature(enable = "avx512f")]
fn ror32(x: __m512i) -> __m512i {
    _mm512_or_si512(_mm512_srli_epi64::<32>(x), _mm512_slli_epi64::<32>(x))
}

#[target_feature(enable = "avx512f")]
fn ror24(x: __m512i) -> __m512i {
    _mm512_or_si512(_mm512_srli_epi64::<24>(x), _mm512_slli_epi64::<40>(x))
}

#[target_feature(enable = "avx512f")]
fn ror16(x: __m512i) -> __m512i {
    _mm512_or_si512(_mm512_srli_epi64::<16>(x), _mm512_slli_epi64::<48>(x))
}

#[target_feature(enable = "avx512f")]
fn ror63(x: __m512i) -> __m512i {
    _mm512_or_si512(_mm512_srli_epi64::<63>(x), _mm512_slli_epi64::<1>(x))
}

#[target_feature(enable = "avx512f")]
fn g1(
    a0: &mut __m512i,
    b0: &mut __m512i,
    c0: &mut __m512i,
    d0: &mut __m512i,
    a1: &mut __m512i,
    b1: &mut __m512i,
    c1: &mut __m512i,
    d1: &mut __m512i,
) {
    *a0 = muladd(*a0, *b0);
    *a1 = muladd(*a1, *b1);
    *d0 = ror32(_mm512_xor_si512(*d0, *a0));
    *d1 = ror32(_mm512_xor_si512(*d1, *a1));
    *c0 = muladd(*c0, *d0);
    *c1 = muladd(*c1, *d1);
    *b0 = ror24(_mm512_xor_si512(*b0, *c0));
    *b1 = ror24(_mm512_xor_si512(*b1, *c1));
}

#[target_feature(enable = "avx512f")]
fn g2(
    a0: &mut __m512i,
    b0: &mut __m512i,
    c0: &mut __m512i,
    d0: &mut __m512i,
    a1: &mut __m512i,
    b1: &mut __m512i,
    c1: &mut __m512i,
    d1: &mut __m512i,
) {
    *a0 = muladd(*a0, *b0);
    *a1 = muladd(*a1, *b1);
    *d0 = ror16(_mm512_xor_si512(*d0, *a0));
    *d1 = ror16(_mm512_xor_si512(*d1, *a1));
    *c0 = muladd(*c0, *d0);
    *c1 = muladd(*c1, *d1);
    *b0 = ror63(_mm512_xor_si512(*b0, *c0));
    *b1 = ror63(_mm512_xor_si512(*b1, *c1));
}

#[target_feature(enable = "avx512f")]
unsafe fn diagonalize(
    b0: &mut __m512i,
    c0: &mut __m512i,
    d0: &mut __m512i,
    b1: &mut __m512i,
    c1: &mut __m512i,
    d1: &mut __m512i,
) {
    *b0 = _mm512_permutex_epi64::<{ shuffle(0, 3, 2, 1) }>(*b0);
    *b1 = _mm512_permutex_epi64::<{ shuffle(0, 3, 2, 1) }>(*b1);
    *c0 = _mm512_permutex_epi64::<{ shuffle(1, 0, 3, 2) }>(*c0);
    *c1 = _mm512_permutex_epi64::<{ shuffle(1, 0, 3, 2) }>(*c1);
    *d0 = _mm512_permutex_epi64::<{ shuffle(2, 1, 0, 3) }>(*d0);
    *d1 = _mm512_permutex_epi64::<{ shuffle(2, 1, 0, 3) }>(*d1);
}

#[target_feature(enable = "avx512f")]
unsafe fn undiagonalize(
    b0: &mut __m512i,
    c0: &mut __m512i,
    d0: &mut __m512i,
    b1: &mut __m512i,
    c1: &mut __m512i,
    d1: &mut __m512i,
) {
    *b0 = _mm512_permutex_epi64::<{ shuffle(2, 1, 0, 3) }>(*b0);
    *b1 = _mm512_permutex_epi64::<{ shuffle(2, 1, 0, 3) }>(*b1);
    *c0 = _mm512_permutex_epi64::<{ shuffle(1, 0, 3, 2) }>(*c0);
    *c1 = _mm512_permutex_epi64::<{ shuffle(1, 0, 3, 2) }>(*c1);
    *d0 = _mm512_permutex_epi64::<{ shuffle(0, 3, 2, 1) }>(*d0);
    *d1 = _mm512_permutex_epi64::<{ shuffle(0, 3, 2, 1) }>(*d1);
}

#[target_feature(enable = "avx512f")]
unsafe fn blake2_round(
    a0: &mut __m512i,
    b0: &mut __m512i,
    c0: &mut __m512i,
    d0: &mut __m512i,
    a1: &mut __m512i,
    b1: &mut __m512i,
    c1: &mut __m512i,
    d1: &mut __m512i,
) {
    // SAFETY: each helper requires only AVX-512F.
    unsafe {
        g1(a0, b0, c0, d0, a1, b1, c1, d1);
        g2(a0, b0, c0, d0, a1, b1, c1, d1);
        diagonalize(b0, c0, d0, b1, c1, d1);
        g1(a0, b0, c0, d0, a1, b1, c1, d1);
        g2(a0, b0, c0, d0, a1, b1, c1, d1);
        undiagonalize(b0, c0, d0, b1, c1, d1);
    }
}

#[target_feature(enable = "avx512f")]
unsafe fn swap_halves(a: &mut __m512i, b: &mut __m512i) {
    let t0 = _mm512_shuffle_i64x2::<{ shuffle(1, 0, 1, 0) }>(*a, *b);
    let t1 = _mm512_shuffle_i64x2::<{ shuffle(3, 2, 3, 2) }>(*a, *b);
    *a = t0;
    *b = t1;
}

#[target_feature(enable = "avx512f")]
unsafe fn swap_quarters(a: &mut __m512i, b: &mut __m512i) {
    // SAFETY: AVX-512F, from the caller's feature gate.
    unsafe {
        swap_halves(a, b);
        let idx = _mm512_setr_epi64(0, 1, 4, 5, 2, 3, 6, 7);
        *a = _mm512_permutexvar_epi64(idx, *a);
        *b = _mm512_permutexvar_epi64(idx, *b);
    }
}

#[target_feature(enable = "avx512f")]
unsafe fn unswap_quarters(a: &mut __m512i, b: &mut __m512i) {
    // SAFETY: AVX-512F, from the caller's feature gate.
    unsafe {
        let idx = _mm512_setr_epi64(0, 1, 4, 5, 2, 3, 6, 7);
        *a = _mm512_permutexvar_epi64(idx, *a);
        *b = _mm512_permutexvar_epi64(idx, *b);
        swap_halves(a, b);
    }
}

/// Column round. The reference's macro binds its arguments `(A0, C0, B0, D0, A1, C1, B1, D1)`.
#[target_feature(enable = "avx512f")]
unsafe fn round1(state: &mut [__m512i; 16], i: usize) {
    let b = 8 * i;
    let (mut a0, mut c0, mut b0, mut d0, mut a1, mut c1, mut b1, mut d1) = (
        state[b],
        state[b + 1],
        state[b + 2],
        state[b + 3],
        state[b + 4],
        state[b + 5],
        state[b + 6],
        state[b + 7],
    );
    // SAFETY: AVX-512F, from the caller's feature gate.
    unsafe {
        swap_halves(&mut a0, &mut b0);
        swap_halves(&mut c0, &mut d0);
        swap_halves(&mut a1, &mut b1);
        swap_halves(&mut c1, &mut d1);
        blake2_round(
            &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
        );
        swap_halves(&mut a0, &mut b0);
        swap_halves(&mut c0, &mut d0);
        swap_halves(&mut a1, &mut b1);
        swap_halves(&mut c1, &mut d1);
    }
    state[b] = a0;
    state[b + 1] = c0;
    state[b + 2] = b0;
    state[b + 3] = d0;
    state[b + 4] = a1;
    state[b + 5] = c1;
    state[b + 6] = b1;
    state[b + 7] = d1;
}

/// Row round. Arguments are `(A0, A1, B0, B1, C0, C1, D0, D1)`.
#[target_feature(enable = "avx512f")]
unsafe fn round2(state: &mut [__m512i; 16], i: usize) {
    let (mut a0, mut a1, mut b0, mut b1, mut c0, mut c1, mut d0, mut d1) = (
        state[i],
        state[2 + i],
        state[4 + i],
        state[6 + i],
        state[8 + i],
        state[10 + i],
        state[12 + i],
        state[14 + i],
    );
    // SAFETY: AVX-512F, from the caller's feature gate.
    unsafe {
        swap_quarters(&mut a0, &mut a1);
        swap_quarters(&mut b0, &mut b1);
        swap_quarters(&mut c0, &mut c1);
        swap_quarters(&mut d0, &mut d1);
        blake2_round(
            &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
        );
        unswap_quarters(&mut a0, &mut a1);
        unswap_quarters(&mut b0, &mut b1);
        unswap_quarters(&mut c0, &mut c1);
        unswap_quarters(&mut d0, &mut d1);
    }
    state[i] = a0;
    state[2 + i] = a1;
    state[4 + i] = b0;
    state[6 + i] = b1;
    state[8 + i] = c0;
    state[10 + i] = c1;
    state[12 + i] = d0;
    state[14 + i] = d1;
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn avx512_matches_scalar() {
        if HaveAvx512F::check().is_none() {
            return;
        }
        let mut prev = Block::zero();
        let mut reference = Block::zero();
        let mut next = Block::zero();
        for i in 0..128 {
            prev.0[i] = (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
            reference.0[i] = (i as u64).wrapping_mul(0x1234_5678_9ABC_DEF0) ^ 0x00FF;
            next.0[i] = 0xFFFF_0000_FFFF_0000 ^ i as u64;
        }
        for with_xor in [false, true] {
            let mut scalar = next;
            let mut wide = next;
            compress_scalar(&mut scalar, &prev, &reference, with_xor);
            // SAFETY: the test returned unless AVX-512F is present, and the
            // blocks are 1024 bytes.
            unsafe { compress_avx512(&mut wide, &prev, &reference, with_xor) };
            assert_eq!(scalar.0, wide.0, "with_xor={with_xor}");
        }
    }
}
