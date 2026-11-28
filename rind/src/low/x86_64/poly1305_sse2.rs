// Copyright (c) 2014, Google Inc.
// SPDX-License-Identifier: ISC
//
// aws-lc's `crypto/poly1305/poly1305_vec.c`, as aws-lc-sys 0.47.0 vendors
// it, in Rust.

//! Poly1305's long runs of whole blocks in SSE2, two blocks a pass in two
//! lanes of 26-bit limbs: a port of BoringSSL's `poly1305_vec.c`, Andrew
//! Moon's poly1305-donna SIMD code, which aws-lc runs on every x86_64 CPU.
//!
//! Its correctness argument is Moon's and Bernstein's "NEON crypto": with
//! blocks m1 to mn, n even, one lane hashes the odd blocks and the other the
//! even ones, each stepping by r², so after a last multiply by r² in the
//! first lane and r in the second their sum is Horner's
//! m1·rⁿ + ... + mn·r. The loop takes four blocks a pass, multiplying each
//! lane by r⁴ and the middle pair by r², as BoringSSL's does. Each limb
//! product is one `pmuludq`, and every sum of them stays under 2^60, as the
//! bounds by each function argue; `low::generic::poly1305`'s tests compare
//! it with the scalar blocks at every length through several passes.
//!
//! Only x86_64 CPUs without SSE4.1 run it: aws-lc's one-pass routines hash
//! on every other. `pmuludq` is one of the multiplies Intel's MXCSR
//! mitigation covers, so `hash` holds an [`Mcdt`].

use core::arch::x86_64::*;
use core::num::Wrapping;

use crate::low::Mcdt;

/// The fewest whole blocks `blocks` hashes in SSE2. aws-lc's lanes start
/// at three; rind keeps shorter runs on the scalar blocks, where the lanes'
/// fixed cost, the powers and the conversions and last multiply, about 250
/// instructions, weighs most. Untimed between 32 B and 1350 B, which both
/// measured no slower.
const MIN_BLOCKS: usize = 8;

const MASK26: u64 = (1 << 26) - 1;

/// r, r², and r⁴ in 26-bit limbs, each lane's multipliers.
#[derive(Clone, Copy)]
pub(crate) struct Powers {
    r4: Power,
    r2: Power,
    /// r² in the first lane and r in the second, for the last multiply.
    r2_r: Power,
}

/// One multiplier per lane: its five limbs, and five times its top four,
/// which multiply the limbs that wrap past 2^130 = 5 (mod p).
#[derive(Clone, Copy)]
struct Power {
    r: [__m128i; 5],
    s: [__m128i; 4],
}

impl Powers {
    /// The powers of the clamped `r`, as `low::generic::poly1305` holds it.
    pub(crate) fn new(r: &[u64; 2]) -> Self {
        let r1 = to_limbs(&[r[0], r[1], 0]);
        let r2 = mul_scalar(&r1, &r1);
        let r4 = mul_scalar(&r2, &r2);
        Self {
            r4: Power::new(&r4, &r4),
            r2: Power::new(&r2, &r2),
            r2_r: Power::new(&r2, &r1),
        }
    }
}

impl Power {
    fn new(first: &[u64; 5], second: &[u64; 5]) -> Self {
        // SAFETY: SSE2 is part of x86_64.
        let lanes = |a: u64, b: u64| unsafe { _mm_set_epi64x(b as i64, a as i64) };
        Self {
            r: core::array::from_fn(|i| lanes(first[i], second[i])),
            // Under 2^26 + 2^5, so five times it fits `pmuludq`'s 32 bits.
            s: core::array::from_fn(|i| {
                lanes(first[i + 1].wrapping_mul(5), second[i + 1].wrapping_mul(5))
            }),
        }
    }
}

/// Hashes `blocks` into `h`, the accumulator in `low::generic::poly1305`'s
/// 64-bit limbs under 2^130 + 2^130/4, whose key `powers` holds, and leaves
/// it so: all but the last one when their count is odd, or none when there
/// are fewer than [`MIN_BLOCKS`]. Returns those it leaves.
#[inline]
pub(crate) fn blocks<'a>(
    h: &mut [u64; 3],
    r: &[u64; 2],
    powers: &mut Option<Powers>,
    blocks: &'a [[u8; 16]],
) -> &'a [[u8; 16]] {
    if blocks.len() < MIN_BLOCKS {
        return blocks;
    }
    let (pairs, rest) = blocks.as_chunks::<2>();
    let powers = powers.get_or_insert_with(|| Powers::new(r));
    hash(h, powers, pairs);
    rest
}

/// Hashes `pairs`, at least one, into `h`.
// Never inlined, so the mitigation it enters covers every `pmuludq` below, as
// `admin/ct-vartime` checks.
#[inline(never)]
fn hash(h: &mut [u64; 3], powers: &Powers, pairs: &[[[u8; 16]; 2]]) {
    let _mcdt = Mcdt::enter();
    let (first, mut pairs) = pairs.split_first().expect("at least one pair");

    // h joins the first block, in the first lane. Its top limb holds h's
    // bits from 104, under 2^27, and the block's 2^24, so the lanes start
    // under 2^28.
    let mut acc = load(first);
    let h_limbs = to_limbs(h);
    for (limb, add) in acc.iter_mut().zip(h_limbs) {
        // SAFETY: SSE2 is part of x86_64.
        *limb = unsafe { _mm_add_epi64(*limb, _mm_set_epi64x(0, add as i64)) };
    }

    while let [a, b, rest @ ..] = pairs {
        let mut t = mul(&acc, &powers.r4);
        add(&mut t, &mul(&load(a), &powers.r2));
        add(&mut t, &load(b));
        acc = reduce(t);
        pairs = rest;
    }
    if let [a] = pairs {
        let mut t = mul(&acc, &powers.r2);
        add(&mut t, &load(a));
        acc = reduce(t);
    }
    let t = reduce(mul(&acc, &powers.r2_r));

    // The lanes' sum, each limb at most 2^27 + 2^12, carried, then back into
    // 64-bit limbs: just over 2^130 at most, so the third is at most 4.
    // SAFETY: SSE2 is part of x86_64.
    let mut sum = t.map(|limb| unsafe {
        let hi = _mm_unpackhi_epi64(limb, limb);
        Wrapping(_mm_cvtsi128_si64(limb) as u64) + Wrapping(_mm_cvtsi128_si64(hi) as u64)
    });
    carry_scalar(&mut sum);
    *h = from_limbs(&sum);
}

/// Two blocks, the first in the first lane, as five 26-bit limbs, each with
/// its 2^128 pad bit.
#[inline(always)]
fn load(pair: &[[u8; 16]; 2]) -> [__m128i; 5] {
    // SAFETY: SSE2 is part of x86_64.
    unsafe {
        let half =
            |i: usize, at: usize| u64::from_le_bytes(pair[i][at..at + 8].try_into().unwrap());
        let lo = _mm_set_epi64x(half(1, 0) as i64, half(0, 0) as i64);
        let hi = _mm_set_epi64x(half(1, 8) as i64, half(0, 8) as i64);
        let mask = _mm_set1_epi64x(MASK26 as i64);
        let mid = _mm_or_si128(_mm_srli_epi64(lo, 52), _mm_slli_epi64(hi, 12));
        [
            _mm_and_si128(lo, mask),
            _mm_and_si128(_mm_srli_epi64(lo, 26), mask),
            _mm_and_si128(mid, mask),
            _mm_and_si128(_mm_srli_epi64(mid, 26), mask),
            _mm_or_si128(_mm_srli_epi64(hi, 40), _mm_set1_epi64x(1 << 24)),
        ]
    }
}

/// The lanes' products, unreduced. With each limb of `a` under 2^28 and of
/// the power under 2^26 + 2^5, as `mul_scalar` leaves them, each of the five
/// sums is under 5 · 2^28 · 5 · 2^26.1 < 2^58.7, and with a block's limbs
/// times r² and the block after added, under 2^60.
#[inline(always)]
fn mul(a: &[__m128i; 5], p: &Power) -> [__m128i; 5] {
    // SAFETY: SSE2 is part of x86_64.
    unsafe {
        let (r, s) = (&p.r, &p.s);
        let m = pmuludq;
        let sum = |terms: [__m128i; 5]| {
            terms
                .into_iter()
                .reduce(|x, y| _mm_add_epi64(x, y))
                .unwrap()
        };
        [
            sum([
                m(a[0], r[0]),
                m(a[1], s[3]),
                m(a[2], s[2]),
                m(a[3], s[1]),
                m(a[4], s[0]),
            ]),
            sum([
                m(a[0], r[1]),
                m(a[1], r[0]),
                m(a[2], s[3]),
                m(a[3], s[2]),
                m(a[4], s[1]),
            ]),
            sum([
                m(a[0], r[2]),
                m(a[1], r[1]),
                m(a[2], r[0]),
                m(a[3], s[3]),
                m(a[4], s[2]),
            ]),
            sum([
                m(a[0], r[3]),
                m(a[1], r[2]),
                m(a[2], r[1]),
                m(a[3], r[0]),
                m(a[4], s[3]),
            ]),
            sum([
                m(a[0], r[4]),
                m(a[1], r[3]),
                m(a[2], r[2]),
                m(a[3], r[1]),
                m(a[4], r[0]),
            ]),
        ]
    }
}

/// The low 32 bits of each lane of `x` times those of `y`, as 64 bits.
// `_mm_mul_epu32` would do, but LLVM lowers it as a 64x32-bit multiply,
// two `pmuludq`, two shifts, and an add, wherever it cannot prove the first
// operand's high half zero, as it cannot for limbs that took a carry: 5.3
// instructions a byte of the 16 KB seal rather than 3.8.
#[inline(always)]
fn pmuludq(mut x: __m128i, y: __m128i) -> __m128i {
    // SAFETY: register-only arithmetic, and SSE2 is part of x86_64.
    unsafe {
        core::arch::asm!(
            "pmuludq {x}, {y}",
            x = inout(xmm_reg) x,
            y = in(xmm_reg) y,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    x
}

#[inline(always)]
fn add(t: &mut [__m128i; 5], x: &[__m128i; 5]) {
    // SAFETY: SSE2 is part of x86_64.
    unsafe {
        for (t, x) in t.iter_mut().zip(x) {
            *t = _mm_add_epi64(*t, *x);
        }
    }
}

/// Carries limbs under 2^60 down to 26 bits, but the second and fifth,
/// which take the last carries after their mask and end under 2^26 + 2^11:
/// the next pass's inputs.
/// BoringSSL's order, with its two chains interleaved, and five times the
/// carry past 2^130 as a shift and an add rather than its `pmuludq`.
#[inline(always)]
fn reduce(mut t: [__m128i; 5]) -> [__m128i; 5] {
    // SAFETY: SSE2 is part of x86_64.
    unsafe {
        let mask = _mm_set1_epi64x(MASK26 as i64);
        let carry = |t: &mut [__m128i; 5], from: usize| {
            let c = _mm_srli_epi64(t[from], 26);
            t[from] = _mm_and_si128(t[from], mask);
            c
        };
        let (c1, c2) = (carry(&mut t, 0), carry(&mut t, 3));
        t[1] = _mm_add_epi64(t[1], c1);
        t[4] = _mm_add_epi64(t[4], c2);
        let (c1, c2) = (carry(&mut t, 1), carry(&mut t, 4));
        t[2] = _mm_add_epi64(t[2], c1);
        t[0] = _mm_add_epi64(t[0], _mm_add_epi64(c2, _mm_slli_epi64(c2, 2)));
        let (c1, c2) = (carry(&mut t, 2), carry(&mut t, 0));
        t[3] = _mm_add_epi64(t[3], c1);
        t[1] = _mm_add_epi64(t[1], c2);
        let c1 = carry(&mut t, 3);
        t[4] = _mm_add_epi64(t[4], c1);
        t
    }
}

/// `h`, in 64-bit limbs and under 2^131, as five 26-bit limbs, but the top
/// one, which takes the bits from 104, under 2^27.
fn to_limbs(h: &[u64; 3]) -> [u64; 5] {
    [
        h[0] & MASK26,
        (h[0] >> 26) & MASK26,
        ((h[0] >> 52) | (h[1] << 12)) & MASK26,
        (h[1] >> 14) & MASK26,
        (h[1] >> 40) | (h[2] << 24),
    ]
}

/// Limbs with the first and the last three under 2^26 and the second at
/// most 2^26, back into 64-bit limbs.
fn from_limbs(l: &[Wrapping<u64>; 5]) -> [u64; 3] {
    let wide = |i: usize, shift: u32| Wrapping((l[i].0 as u128) << shift);
    let low = wide(0, 0) + wide(1, 26) + wide(2, 52) + wide(3, 78);
    let (low, carry) = low
        .0
        .overflowing_add(((l[4].0 & ((1 << 24) - 1)) as u128) << 104);
    [
        low as u64,
        (low >> 64) as u64,
        (l[4].0 >> 24).wrapping_add(carry as u64),
    ]
}

/// Carries `d`, five limbs under 2^63, down to 26 bits each, but the second,
/// which takes the last carry: poly1305-donna-32's carry.
fn carry_scalar(d: &mut [Wrapping<u64>; 5]) {
    for i in 0..4 {
        d[i + 1] += d[i] >> 26;
        d[i] &= Wrapping(MASK26);
    }
    d[0] += (d[4] >> 26) * Wrapping(5);
    d[4] &= Wrapping(MASK26);
    d[1] += d[0] >> 26;
    d[0] &= Wrapping(MASK26);
}

/// `a·b mod p`, from limbs under 2^26 + 2^5, carried so each is under 2^26
/// but the second, under 2^26 + 2^5: poly1305-donna-32's multiply. Each sum
/// of products is under 5 · 2^26.1 · 5 · 2^26.1 < 2^57.
fn mul_scalar(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
    let (a, b) = (a.map(Wrapping), b.map(Wrapping));
    let s = b.map(|x| x * Wrapping(5));
    let mut d = [
        a[0] * b[0] + a[1] * s[4] + a[2] * s[3] + a[3] * s[2] + a[4] * s[1],
        a[0] * b[1] + a[1] * b[0] + a[2] * s[4] + a[3] * s[3] + a[4] * s[2],
        a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + a[3] * s[4] + a[4] * s[3],
        a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + a[4] * s[4],
        a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0],
    ];
    carry_scalar(&mut d);
    d.map(|x| x.0)
}
