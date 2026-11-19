// Ported from the Argon2 reference implementation, Copyright 2015 Daniel
// Dinu, Dmitry Khovratovich, Jean-Philippe Aumasson, and Samuel Neves, under
// CC0-1.0.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on SSSE3.
//!
//! A port of the reference implementation's 128-bit `BLAKE2_ROUND`
//! (`blamka-round-opt.h`), the same permutation `d6114f56` runs on x86_64
//! without AVX2. Dispatch selects it when the CPU has SSSE3 and lacks the
//! AVX2 set: it beat the portable permutation by 1.12x to 1.2x on the CPUs
//! tried, with AVX2 denied (see quest/m4/protocols/argon2-simd.md).

use core::arch::x86_64::*;

use crate::low::generic::argon2::Argon2Block;

/// # Safety
/// The CPU must have SSSE3. Each block is 1024 bytes.
#[target_feature(enable = "ssse3")]
pub(crate) unsafe fn compress(x: &Argon2Block, y: &Argon2Block, out: &mut Argon2Block, xor: bool) {
    // SAFETY: the caller proved SSSE3, and these are the same blocks.
    unsafe { compress_ssse3(out, x, y, xor) }
}

// `_MM_SHUFFLE` as the C headers spell it.
const fn shuffle(z: i32, y: i32, x: i32, w: i32) -> i32 {
    (z << 6) | (y << 4) | (x << 2) | w
}

#[target_feature(enable = "ssse3")]
unsafe fn compress_ssse3(
    next: &mut Argon2Block,
    prev: &Argon2Block,
    reference: &Argon2Block,
    with_xor: bool,
) {
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
unsafe fn load128(block: &Argon2Block) -> [__m128i; 64] {
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
    use crate::low::generic::argon2::assert_matches_portable;
    use crate::low::x86_64::cpu::HaveSsse3;

    #[test]
    fn matches_portable() {
        if HaveSsse3::check().is_none() {
            return;
        }
        assert_matches_portable(|x, y, out, xor| {
            // SAFETY: SSSE3 checked above, and the blocks are 1024 bytes.
            unsafe { compress(x, y, out, xor) }
        });
    }
}
