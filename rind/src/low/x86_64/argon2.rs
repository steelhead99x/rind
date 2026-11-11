// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on x86_64.
//!
//! The permutations are the Argon2 reference implementation's `fill_block`,
//! copyright 2015 Daniel Dinu, Dmitry Khovratovich, Jean-Philippe Aumasson, and
//! Samuel Neves, used under Apache-2.0 (also offered as CC0-1.0), from
//! `opt.c` and `blamka-round-opt.h`. The lane shuffles are that code's, so a
//! block each one returns matches the scalar permutation.

use core::arch::x86_64::*;

use super::cpu::{HaveAvx2, HaveAvx512F, HaveSsse3};
use crate::low::argon2::{Block, compress as compress_scalar};

/// `G(prev, reference)`.
///
/// AVX-512F, then the AVX2 set [`HaveAvx2`] names (AVX, AVX2, BMI1, BMI2,
/// POPCNT, and SSSE3), then SSSE3, then the portable permutation. Each step is
/// that feature's check. A CPU without the wider feature does not run it, and
/// the portable permutation runs only when SSSE3 is absent too.
pub(crate) fn compress(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    if HaveAvx512F::check().is_some() {
        // SAFETY: `HaveAvx512F` is proof of AVX-512F, and the blocks are 1024
        // bytes each, which the loads and stores stay inside.
        unsafe { compress_avx512(next, prev, reference, with_xor) };
    } else if HaveAvx2::check().is_some() {
        // SAFETY: `HaveAvx2` is proof of AVX2, which this permutation uses.
        unsafe { compress_avx2(next, prev, reference, with_xor) };
    } else if HaveSsse3::check().is_some() {
        // SAFETY: `HaveSsse3` is proof of SSSE3, which this permutation uses.
        unsafe { compress_ssse3(next, prev, reference, with_xor) };
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

// --- AVX2. The reference's `BLAKE2_ROUND_1` and `BLAKE2_ROUND_2`. ---

#[target_feature(enable = "avx2")]
unsafe fn compress_avx2(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    // SAFETY: `prev` is 1024 bytes, as `load256` requires.
    let mut state = unsafe { load256(prev) };
    let mut xy = [core::mem::MaybeUninit::<__m256i>::uninit(); 32];
    // SAFETY: each block is 1024 bytes, thirty-two 32-byte lanes. Every `xy`
    // lane is written before it is read.
    unsafe {
        for i in 0..32 {
            let r = _mm256_loadu_si256(reference.0.as_ptr().add(i * 4).cast());
            state[i] = _mm256_xor_si256(state[i], r);
            xy[i].write(if with_xor {
                let n = _mm256_loadu_si256(next.0.as_ptr().add(i * 4).cast());
                _mm256_xor_si256(state[i], n)
            } else {
                state[i]
            });
        }
        let xy = core::mem::transmute::<[core::mem::MaybeUninit<__m256i>; 32], [__m256i; 32]>(xy);
        for i in 0..4 {
            avx2_round1(&mut state, i);
        }
        for i in 0..4 {
            avx2_round2(&mut state, i);
        }
        for i in 0..32 {
            state[i] = _mm256_xor_si256(state[i], xy[i]);
            _mm256_storeu_si256(next.0.as_mut_ptr().add(i * 4).cast(), state[i]);
        }
    }
}

#[target_feature(enable = "avx2")]
unsafe fn load256(block: &Block) -> [__m256i; 32] {
    let mut state = [core::mem::MaybeUninit::<__m256i>::uninit(); 32];
    // SAFETY: `block` is 1024 bytes, and every lane is written before the
    // array is read as initialized.
    unsafe {
        for (i, lane) in state.iter_mut().enumerate() {
            lane.write(_mm256_loadu_si256(block.0.as_ptr().add(i * 4).cast()));
        }
        core::mem::transmute(state)
    }
}

#[target_feature(enable = "avx2")]
fn avx2_blamka(x: __m256i, y: __m256i) -> __m256i {
    let z = _mm256_mul_epu32(x, y);
    _mm256_add_epi64(_mm256_add_epi64(x, y), _mm256_add_epi64(z, z))
}

#[target_feature(enable = "avx2")]
fn avx2_rotr32(x: __m256i) -> __m256i {
    _mm256_shuffle_epi32::<{ shuffle(2, 3, 0, 1) }>(x)
}

#[target_feature(enable = "avx2")]
fn avx2_rotr24(x: __m256i) -> __m256i {
    let control = _mm256_setr_epi8(
        3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10, 3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13,
        14, 15, 8, 9, 10,
    );
    _mm256_shuffle_epi8(x, control)
}

#[target_feature(enable = "avx2")]
fn avx2_rotr16(x: __m256i) -> __m256i {
    let control = _mm256_setr_epi8(
        2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9, 2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12,
        13, 14, 15, 8, 9,
    );
    _mm256_shuffle_epi8(x, control)
}

#[target_feature(enable = "avx2")]
fn avx2_rotr63(x: __m256i) -> __m256i {
    _mm256_xor_si256(_mm256_srli_epi64::<63>(x), _mm256_add_epi64(x, x))
}

/// The reference's `G1_AVX2`: BlaMka on `(A0, B0, C0, D0)`, then on `(A1, B1, C1, D1)`.
#[target_feature(enable = "avx2")]
fn avx2_g1(
    a0: &mut __m256i,
    a1: &mut __m256i,
    b0: &mut __m256i,
    b1: &mut __m256i,
    c0: &mut __m256i,
    c1: &mut __m256i,
    d0: &mut __m256i,
    d1: &mut __m256i,
) {
    *a0 = avx2_blamka(*a0, *b0);
    *d0 = avx2_rotr32(_mm256_xor_si256(*d0, *a0));
    *c0 = avx2_blamka(*c0, *d0);
    *b0 = avx2_rotr24(_mm256_xor_si256(*b0, *c0));

    *a1 = avx2_blamka(*a1, *b1);
    *d1 = avx2_rotr32(_mm256_xor_si256(*d1, *a1));
    *c1 = avx2_blamka(*c1, *d1);
    *b1 = avx2_rotr24(_mm256_xor_si256(*b1, *c1));
}

/// The reference's `G2_AVX2`.
#[target_feature(enable = "avx2")]
fn avx2_g2(
    a0: &mut __m256i,
    a1: &mut __m256i,
    b0: &mut __m256i,
    b1: &mut __m256i,
    c0: &mut __m256i,
    c1: &mut __m256i,
    d0: &mut __m256i,
    d1: &mut __m256i,
) {
    *a0 = avx2_blamka(*a0, *b0);
    *d0 = avx2_rotr16(_mm256_xor_si256(*d0, *a0));
    *c0 = avx2_blamka(*c0, *d0);
    *b0 = avx2_rotr63(_mm256_xor_si256(*b0, *c0));

    *a1 = avx2_blamka(*a1, *b1);
    *d1 = avx2_rotr16(_mm256_xor_si256(*d1, *a1));
    *c1 = avx2_blamka(*c1, *d1);
    *b1 = avx2_rotr63(_mm256_xor_si256(*b1, *c1));
}

/// The reference's `DIAGONALIZE_1`. `A0` and `A1` stay where they are.
#[target_feature(enable = "avx2")]
fn avx2_diagonalize_1(
    b0: &mut __m256i,
    c0: &mut __m256i,
    d0: &mut __m256i,
    b1: &mut __m256i,
    c1: &mut __m256i,
    d1: &mut __m256i,
) {
    *b0 = _mm256_permute4x64_epi64::<{ shuffle(0, 3, 2, 1) }>(*b0);
    *c0 = _mm256_permute4x64_epi64::<{ shuffle(1, 0, 3, 2) }>(*c0);
    *d0 = _mm256_permute4x64_epi64::<{ shuffle(2, 1, 0, 3) }>(*d0);
    *b1 = _mm256_permute4x64_epi64::<{ shuffle(0, 3, 2, 1) }>(*b1);
    *c1 = _mm256_permute4x64_epi64::<{ shuffle(1, 0, 3, 2) }>(*c1);
    *d1 = _mm256_permute4x64_epi64::<{ shuffle(2, 1, 0, 3) }>(*d1);
}

/// The reference's `UNDIAGONALIZE_1`.
#[target_feature(enable = "avx2")]
fn avx2_undiagonalize_1(
    b0: &mut __m256i,
    c0: &mut __m256i,
    d0: &mut __m256i,
    b1: &mut __m256i,
    c1: &mut __m256i,
    d1: &mut __m256i,
) {
    *b0 = _mm256_permute4x64_epi64::<{ shuffle(2, 1, 0, 3) }>(*b0);
    *c0 = _mm256_permute4x64_epi64::<{ shuffle(1, 0, 3, 2) }>(*c0);
    *d0 = _mm256_permute4x64_epi64::<{ shuffle(0, 3, 2, 1) }>(*d0);
    *b1 = _mm256_permute4x64_epi64::<{ shuffle(2, 1, 0, 3) }>(*b1);
    *c1 = _mm256_permute4x64_epi64::<{ shuffle(1, 0, 3, 2) }>(*c1);
    *d1 = _mm256_permute4x64_epi64::<{ shuffle(0, 3, 2, 1) }>(*d1);
}

/// The reference's `DIAGONALIZE_2`.
#[target_feature(enable = "avx2")]
fn avx2_diagonalize_2(
    b0: &mut __m256i,
    b1: &mut __m256i,
    c0: &mut __m256i,
    c1: &mut __m256i,
    d0: &mut __m256i,
    d1: &mut __m256i,
) {
    let tmp1 = _mm256_blend_epi32::<0xCC>(*b0, *b1);
    let tmp2 = _mm256_blend_epi32::<0x33>(*b0, *b1);
    *b1 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp1);
    *b0 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp2);
    core::mem::swap(c0, c1);
    let tmp1 = _mm256_blend_epi32::<0xCC>(*d0, *d1);
    let tmp2 = _mm256_blend_epi32::<0x33>(*d0, *d1);
    *d0 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp1);
    *d1 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp2);
}

/// The reference's `UNDIAGONALIZE_2`.
#[target_feature(enable = "avx2")]
fn avx2_undiagonalize_2(
    b0: &mut __m256i,
    b1: &mut __m256i,
    c0: &mut __m256i,
    c1: &mut __m256i,
    d0: &mut __m256i,
    d1: &mut __m256i,
) {
    let tmp1 = _mm256_blend_epi32::<0xCC>(*b0, *b1);
    let tmp2 = _mm256_blend_epi32::<0x33>(*b0, *b1);
    *b0 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp1);
    *b1 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp2);
    core::mem::swap(c0, c1);
    let tmp1 = _mm256_blend_epi32::<0x33>(*d0, *d1);
    let tmp2 = _mm256_blend_epi32::<0xCC>(*d0, *d1);
    *d0 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp1);
    *d1 = _mm256_permute4x64_epi64::<{ shuffle(2, 3, 0, 1) }>(tmp2);
}

/// `BLAKE2_ROUND_1` over lanes `(8i+0, 8i+4, 8i+1, 8i+5, 8i+2, 8i+6, 8i+3, 8i+7)`.
#[target_feature(enable = "avx2")]
fn avx2_round1(state: &mut [__m256i; 32], i: usize) {
    let b = 8 * i;
    let (mut a0, mut a1, mut b0, mut b1, mut c0, mut c1, mut d0, mut d1) = (
        state[b],
        state[b + 4],
        state[b + 1],
        state[b + 5],
        state[b + 2],
        state[b + 6],
        state[b + 3],
        state[b + 7],
    );
    avx2_g1(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_g2(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_diagonalize_1(&mut b0, &mut c0, &mut d0, &mut b1, &mut c1, &mut d1);
    avx2_g1(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_g2(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_undiagonalize_1(&mut b0, &mut c0, &mut d0, &mut b1, &mut c1, &mut d1);
    state[b] = a0;
    state[b + 4] = a1;
    state[b + 1] = b0;
    state[b + 5] = b1;
    state[b + 2] = c0;
    state[b + 6] = c1;
    state[b + 3] = d0;
    state[b + 7] = d1;
}

/// `BLAKE2_ROUND_2` over lanes `(i, 4+i, 8+i, 12+i, 16+i, 20+i, 24+i, 28+i)`.
#[target_feature(enable = "avx2")]
fn avx2_round2(state: &mut [__m256i; 32], i: usize) {
    let (mut a0, mut a1, mut b0, mut b1, mut c0, mut c1, mut d0, mut d1) = (
        state[i],
        state[4 + i],
        state[8 + i],
        state[12 + i],
        state[16 + i],
        state[20 + i],
        state[24 + i],
        state[28 + i],
    );
    avx2_g1(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_g2(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_diagonalize_2(&mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1);
    avx2_g1(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_g2(
        &mut a0, &mut a1, &mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1,
    );
    avx2_undiagonalize_2(&mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1);
    state[i] = a0;
    state[4 + i] = a1;
    state[8 + i] = b0;
    state[12 + i] = b1;
    state[16 + i] = c0;
    state[20 + i] = c1;
    state[24 + i] = d0;
    state[28 + i] = d1;
}

// --- SSSE3. The reference's 128-bit `BLAKE2_ROUND`, twice. ---

#[target_feature(enable = "ssse3")]
unsafe fn compress_ssse3(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    // SAFETY: `prev` is 1024 bytes, as `load128` requires.
    let mut state = unsafe { load128(prev) };
    let mut xy = [core::mem::MaybeUninit::<__m128i>::uninit(); 64];
    // SAFETY: each block is 1024 bytes, sixty-four 16-byte lanes. Every `xy`
    // lane is written before it is read.
    unsafe {
        for i in 0..64 {
            let r = _mm_loadu_si128(reference.0.as_ptr().add(i * 2).cast());
            state[i] = _mm_xor_si128(state[i], r);
            xy[i].write(if with_xor {
                let n = _mm_loadu_si128(next.0.as_ptr().add(i * 2).cast());
                _mm_xor_si128(state[i], n)
            } else {
                state[i]
            });
        }
        let xy = core::mem::transmute::<[core::mem::MaybeUninit<__m128i>; 64], [__m128i; 64]>(xy);
        for i in 0..8 {
            ssse3_round(
                &mut state,
                8 * i,
                8 * i + 1,
                8 * i + 2,
                8 * i + 3,
                8 * i + 4,
                8 * i + 5,
                8 * i + 6,
                8 * i + 7,
            );
        }
        for i in 0..8 {
            ssse3_round(
                &mut state,
                i,
                8 + i,
                16 + i,
                24 + i,
                32 + i,
                40 + i,
                48 + i,
                56 + i,
            );
        }
        for i in 0..64 {
            state[i] = _mm_xor_si128(state[i], xy[i]);
            _mm_storeu_si128(next.0.as_mut_ptr().add(i * 2).cast(), state[i]);
        }
    }
}

#[target_feature(enable = "ssse3")]
unsafe fn load128(block: &Block) -> [__m128i; 64] {
    let mut state = [core::mem::MaybeUninit::<__m128i>::uninit(); 64];
    // SAFETY: `block` is 1024 bytes, and every lane is written before the
    // array is read as initialized.
    unsafe {
        for (i, lane) in state.iter_mut().enumerate() {
            lane.write(_mm_loadu_si128(block.0.as_ptr().add(i * 2).cast()));
        }
        core::mem::transmute(state)
    }
}

#[target_feature(enable = "ssse3")]
fn ssse3_blamka(x: __m128i, y: __m128i) -> __m128i {
    let z = _mm_mul_epu32(x, y);
    _mm_add_epi64(_mm_add_epi64(x, y), _mm_add_epi64(z, z))
}

#[target_feature(enable = "ssse3")]
fn ssse3_rotr32(x: __m128i) -> __m128i {
    _mm_shuffle_epi32::<{ shuffle(2, 3, 0, 1) }>(x)
}

#[target_feature(enable = "ssse3")]
fn ssse3_rotr24(x: __m128i) -> __m128i {
    let control = _mm_setr_epi8(3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10);
    _mm_shuffle_epi8(x, control)
}

#[target_feature(enable = "ssse3")]
fn ssse3_rotr16(x: __m128i) -> __m128i {
    let control = _mm_setr_epi8(2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9);
    _mm_shuffle_epi8(x, control)
}

#[target_feature(enable = "ssse3")]
fn ssse3_rotr63(x: __m128i) -> __m128i {
    _mm_xor_si128(_mm_srli_epi64::<63>(x), _mm_add_epi64(x, x))
}

#[target_feature(enable = "ssse3")]
fn ssse3_g1(
    a0: &mut __m128i,
    b0: &mut __m128i,
    c0: &mut __m128i,
    d0: &mut __m128i,
    a1: &mut __m128i,
    b1: &mut __m128i,
    c1: &mut __m128i,
    d1: &mut __m128i,
) {
    *a0 = ssse3_blamka(*a0, *b0);
    *a1 = ssse3_blamka(*a1, *b1);
    *d0 = ssse3_rotr32(_mm_xor_si128(*d0, *a0));
    *d1 = ssse3_rotr32(_mm_xor_si128(*d1, *a1));
    *c0 = ssse3_blamka(*c0, *d0);
    *c1 = ssse3_blamka(*c1, *d1);
    *b0 = ssse3_rotr24(_mm_xor_si128(*b0, *c0));
    *b1 = ssse3_rotr24(_mm_xor_si128(*b1, *c1));
}

#[target_feature(enable = "ssse3")]
fn ssse3_g2(
    a0: &mut __m128i,
    b0: &mut __m128i,
    c0: &mut __m128i,
    d0: &mut __m128i,
    a1: &mut __m128i,
    b1: &mut __m128i,
    c1: &mut __m128i,
    d1: &mut __m128i,
) {
    *a0 = ssse3_blamka(*a0, *b0);
    *a1 = ssse3_blamka(*a1, *b1);
    *d0 = ssse3_rotr16(_mm_xor_si128(*d0, *a0));
    *d1 = ssse3_rotr16(_mm_xor_si128(*d1, *a1));
    *c0 = ssse3_blamka(*c0, *d0);
    *c1 = ssse3_blamka(*c1, *d1);
    *b0 = ssse3_rotr63(_mm_xor_si128(*b0, *c0));
    *b1 = ssse3_rotr63(_mm_xor_si128(*b1, *c1));
}

/// The reference's SSSE3 `DIAGONALIZE`, `alignr` by 8 bytes.
#[target_feature(enable = "ssse3")]
fn ssse3_diagonalize(
    b0: &mut __m128i,
    b1: &mut __m128i,
    c0: &mut __m128i,
    c1: &mut __m128i,
    d0: &mut __m128i,
    d1: &mut __m128i,
) {
    let t0 = _mm_alignr_epi8::<8>(*b1, *b0);
    let t1 = _mm_alignr_epi8::<8>(*b0, *b1);
    *b0 = t0;
    *b1 = t1;
    core::mem::swap(c0, c1);
    let t0 = _mm_alignr_epi8::<8>(*d1, *d0);
    let t1 = _mm_alignr_epi8::<8>(*d0, *d1);
    *d0 = t1;
    *d1 = t0;
}

/// The reference's SSSE3 `UNDIAGONALIZE`.
#[target_feature(enable = "ssse3")]
fn ssse3_undiagonalize(
    b0: &mut __m128i,
    b1: &mut __m128i,
    c0: &mut __m128i,
    c1: &mut __m128i,
    d0: &mut __m128i,
    d1: &mut __m128i,
) {
    let t0 = _mm_alignr_epi8::<8>(*b0, *b1);
    let t1 = _mm_alignr_epi8::<8>(*b1, *b0);
    *b0 = t0;
    *b1 = t1;
    core::mem::swap(c0, c1);
    let t0 = _mm_alignr_epi8::<8>(*d0, *d1);
    let t1 = _mm_alignr_epi8::<8>(*d1, *d0);
    *d0 = t1;
    *d1 = t0;
}

/// One `BLAKE2_ROUND`. Arguments are `(A0, A1, B0, B1, C0, C1, D0, D1)`.
#[target_feature(enable = "ssse3")]
fn ssse3_round(
    state: &mut [__m128i; 64],
    a0i: usize,
    a1i: usize,
    b0i: usize,
    b1i: usize,
    c0i: usize,
    c1i: usize,
    d0i: usize,
    d1i: usize,
) {
    let (mut a0, mut a1, mut b0, mut b1, mut c0, mut c1, mut d0, mut d1) = (
        state[a0i], state[a1i], state[b0i], state[b1i], state[c0i], state[c1i], state[d0i],
        state[d1i],
    );
    ssse3_g1(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    ssse3_g2(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    ssse3_diagonalize(&mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1);
    ssse3_g1(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    ssse3_g2(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    ssse3_undiagonalize(&mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1);
    state[a0i] = a0;
    state[a1i] = a1;
    state[b0i] = b0;
    state[b1i] = b1;
    state[c0i] = c0;
    state[c1i] = c1;
    state[d0i] = d0;
    state[d1i] = d1;
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn blocks(seed: u64) -> (Block, Block, Block) {
        let mut prev = Block::zero();
        let mut reference = Block::zero();
        let mut next = Block::zero();
        for i in 0..128 {
            prev.0[i] = (i as u64).wrapping_mul(seed);
            reference.0[i] = (i as u64).wrapping_mul(seed ^ 0x1234_5678_9ABC_DEF0) ^ 0x00FF;
            next.0[i] = 0xFFFF_0000_FFFF_0000 ^ seed.wrapping_add(i as u64);
        }
        (prev, reference, next)
    }

    fn matches_scalar(run: unsafe fn(&mut Block, &Block, &Block, bool)) {
        for seed in [0x9E37_79B9_7F4A_7C15, 1] {
            let (prev, reference, next) = blocks(seed);
            for with_xor in [false, true] {
                let mut scalar = next;
                let mut wide = next;
                compress_scalar(&mut scalar, &prev, &reference, with_xor);
                // SAFETY: the caller returned unless this CPU has the feature
                // the permutation uses, and the blocks are 1024 bytes.
                unsafe { run(&mut wide, &prev, &reference, with_xor) };
                assert_eq!(scalar.0, wide.0, "seed={seed:#x} with_xor={with_xor}");
            }
        }
    }

    #[test]
    fn avx512_matches_scalar() {
        if HaveAvx512F::check().is_none() {
            return;
        }
        matches_scalar(compress_avx512);
    }

    #[test]
    fn avx2_matches_scalar() {
        if HaveAvx2::check().is_none() {
            return;
        }
        matches_scalar(compress_avx2);
    }

    #[test]
    fn ssse3_matches_scalar() {
        if HaveSsse3::check().is_none() {
            return;
        }
        matches_scalar(compress_ssse3);
    }

    /// The dispatcher runs the widest permutation this CPU has, and that
    /// permutation agrees with the portable one.
    #[test]
    fn dispatcher_matches_scalar() {
        let (prev, reference, next) = blocks(0xA5A5_A5A5_A5A5_A5A5);
        for with_xor in [false, true] {
            let mut scalar = next;
            let mut chosen = next;
            compress_scalar(&mut scalar, &prev, &reference, with_xor);
            compress(&mut chosen, &prev, &reference, with_xor);
            assert_eq!(scalar.0, chosen.0, "with_xor={with_xor}");
        }
    }

    // Valgrind decodes no AVX-512, so `admin/ct-sde` traces the permutation
    // here. The loads and stores cover the whole block, whichever words it holds.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_argon2_avx512() {
        use crate::low::x86_64::ct_sde;

        assert!(HaveAvx512F::check().is_some(), "AVX-512F");
        let (prev, reference, next) = blocks(ct_sde::seed());
        let word = ct_sde::traced(|| {
            let mut wide = next;
            // SAFETY: the assertion is proof of AVX-512F, and the blocks are
            // 1024 bytes.
            unsafe { compress_avx512(&mut wide, &prev, &reference, true) };
            wide.0[0]
        });
        core::hint::black_box(word);
    }
}
