// Copyright (c) 2016-2021 isis agora lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// SPDX-License-Identifier: BSD-3-Clause

//! Ed25519 verification's `[b]B + [s0]P0 + [s1]P1` on CPUs with AVX2 but
//! without ADX, ported from curve25519-dalek 5.0.0's AVX2 backend: its field
//! arithmetic (`backend/vector/avx2/field.rs`), its parallel point formulas
//! (`backend/vector/avx2/edwards.rs`), and its table of the base point's odd
//! multiples, with a second for `[2^128]B`. The loop is
//! `low::generic::edwards25519_msm`'s, over the same non-adjacent forms.
//!
//! The scalars and the points are public, so that runs in variable time.
//! [`edwards25519_mul`] runs the same formulas in constant time for one
//! secret scalar and point, as curve25519-dalek's variable-base multiplication
//! does: a fixed window of four bits over signed digits, with each digit's
//! table entry read through masks.
//!
//! Each `Fe4` holds four field elements (lanes A, B, C, D) in radix
//! 2^25.5: ten limbs, alternately 26 and 25 bits, each limb pair's four
//! lanes interleaved in one vector as `(a0, b0, a1, b1, c0, d0, c1, d1)`.
//! Every operation's bound on its inputs' limbs is dalek's, which its
//! documentation gives with the formulas' derivation.

use core::arch::x86_64::*;

use super::cpu::HaveAvx2;
use crate::low::generic::edwards25519_msm::non_adjacent_form;

/// Computes `res := [base]B + [scalars[0]]points[0] + [scalars[1]]points[1]`
/// as `low::generic::edwards25519_msm` does.
pub(crate) fn edwards25519_msm(
    res: &mut [u64; 12],
    base: &[u64; 4],
    scalars: &[[u64; 4]; 2],
    points: &[[u64; 16]; 2],
    _token: HaveAvx2,
) {
    assert!(scalars.iter().all(|s| s[3] >> 63 == 0));
    let coordinates = |p: &[u64; 16]| -> [[u64; 4]; 4] {
        core::array::from_fn(|i| p[4 * i..4 * i + 4].try_into().unwrap())
    };

    // SAFETY: `_token` proves the `avx` and `avx2` cpu features
    let q = unsafe { msm(base, scalars, &points.each_ref().map(coordinates)) };
    for (out, coordinate) in res.as_chunks_mut::<4>().0.iter_mut().zip(q) {
        out.copy_from_slice(&coordinate);
    }
}

/// Computes `[base]B + [s0]P0 + [s1]P1` from the points' extended
/// coordinates `(X, Y, Z, T)`, returning the result's `(X, Y, Z)`, each
/// reduced.
#[target_feature(enable = "avx,avx2")]
fn msm(base: &[u64; 4], scalars: &[[u64; 4]; 2], points: &[[[u64; 4]; 4]; 2]) -> [[u64; 4]; 3] {
    // Its operands are public, but `admin/ct-vartime` holds every `vpmuludq`
    // to Intel's MXCSR mitigation alike. `target_feature` keeps this from
    // inlining into its caller, so the mitigation covers only the vector work.
    let _mcdt = crate::low::Mcdt::enter();
    let nafs = [
        non_adjacent_form(&[base[0], base[1], 0, 0], 8),
        non_adjacent_form(&[base[2], base[3], 0, 0], 8),
        non_adjacent_form(&scalars[0], 5),
        non_adjacent_form(&scalars[1], 5),
    ];
    let tables = [odd_multiples(&points[0]), odd_multiples(&points[1])];

    let top = (0..256).rev().find(|&i| nafs.iter().any(|naf| naf[i] != 0));
    let mut q = Extended(Fe4(EXTENDED_IDENTITY));
    for i in (0..=top.unwrap_or(0)).rev() {
        q = q.double();
        for (j, naf) in nafs.iter().enumerate() {
            let entry = |d: i8| match j {
                0 => Cached(Fe4(BASE_ODD_MULTIPLES[d.unsigned_abs() as usize / 2])),
                1 => Cached(Fe4(BASE128_ODD_MULTIPLES[d.unsigned_abs() as usize / 2])),
                _ => tables[j - 2][d.unsigned_abs() as usize / 2],
            };
            match naf[i] {
                0 => {}
                d if d > 0 => q = q.add(&entry(d)),
                d => q = q.add(&entry(d).neg()),
            }
        }
    }

    let [x, y, z, _] = q.0.split();
    [x, y, z]
}

/// Computes `res := [scalar]P` in constant time, from the scalar's signed
/// radix-16 digits (each in `-8..=8`, least significant first) and the
/// point's reduced extended coordinates `(X, Y, Z, T)`, as reduced extended
/// coordinates.
pub(crate) fn edwards25519_mul(
    res: &mut [u64; 16],
    digits: &[i8; 64],
    point: &[u64; 16],
    _token: HaveAvx2,
) {
    let coordinates: [[u64; 4]; 4] =
        core::array::from_fn(|i| point[4 * i..4 * i + 4].try_into().unwrap());
    // SAFETY: `_token` proves the `avx` and `avx2` cpu features
    let q = unsafe { mul(digits, &coordinates) };
    for (out, coordinate) in res.as_chunks_mut::<4>().0.iter_mut().zip(q) {
        out.copy_from_slice(&coordinate);
    }
}

/// `[scalar]P`: the table of `P ..= 8P`, then for each digit from the top,
/// sixteen times the sum so far plus the digit's entry.
#[target_feature(enable = "avx,avx2")]
fn mul(digits: &[i8; 64], point: &[[u64; 4]; 4]) -> [[u64; 4]; 4] {
    // The operands are secret: `vpmuludq` runs under Intel's MXCSR
    // mitigation, as in `msm`.
    let _mcdt = crate::low::Mcdt::enter();
    let p1 = Extended(Fe4::new(point));
    let mut extended = [p1; 8];
    let mut table = [Cached::from(p1); 8];
    for i in 1..8 {
        // Entry `i` is `(i + 1) * P`.
        extended[i] = match i % 2 {
            1 => extended[i / 2].double(),
            _ => extended[i - 1].add(&table[0]),
        };
        table[i] = Cached::from(extended[i]);
    }

    let mut q = Extended(Fe4(EXTENDED_IDENTITY)).add(&select(&table, digits[63]));
    for digit in digits[..63].iter().rev() {
        for _ in 0..4 {
            q = q.double();
        }
        q = q.add(&select(&table, *digit));
    }
    q.0.split()
}

/// `[digit]P` as a [`Cached`] point, from `table`'s `P ..= 8P`, for
/// `-8 <= digit <= 8`, in constant time.
#[target_feature(enable = "avx,avx2")]
fn select(table: &[Cached; 8], digit: i8) -> Cached {
    // 0 or -1, by an arithmetic shift, so no branch reads the digit.
    let sign = (digit >> 7) as i32;
    let magnitude = _mm256_set1_epi32((digit as i32 ^ sign).wrapping_sub(sign));

    let mut out = CACHED_IDENTITY;
    for (i, entry) in table.iter().enumerate() {
        let hit = _mm256_cmpeq_epi32(magnitude, _mm256_set1_epi32(i as i32 + 1));
        for (out, entry) in out.iter_mut().zip(entry.0.0) {
            *out = _mm256_blendv_epi8(*out, entry, hit);
        }
    }

    let negated = Cached(Fe4(out)).neg();
    let negative = _mm256_set1_epi32(sign);
    for (out, negated) in out.iter_mut().zip(negated.0.0) {
        *out = _mm256_blendv_epi8(*out, negated, negative);
    }
    Cached(Fe4(out))
}

/// `[P, 3P, 5P, ..., 15P]`, the odd multiples a width-5 form's digits take.
#[target_feature(enable = "avx,avx2")]
fn odd_multiples(point: &[[u64; 4]; 4]) -> [Cached; 8] {
    let p1 = Extended(Fe4::new(point));
    let p2 = p1.double();
    let mut table = [Cached::from(p1); 8];
    for i in 0..7 {
        table[i + 1] = Cached::from(p2.add(&table[i]));
    }
    table
}

/// A point in extended twisted Edwards coordinates `(X, Y, Z, T)`.
#[derive(Clone, Copy)]
struct Extended(Fe4);

/// A point as `(Y - X, Y + X, 2Z, 2dT)` scaled by 121666, which makes
/// `d = -121665/121666` an integer, ready to add to an [`Extended`].
#[derive(Clone, Copy)]
struct Cached(Fe4);

impl Extended {
    #[target_feature(enable = "avx,avx2")]
    fn double(&self) -> Self {
        let mut tmp0 = self.0.shuffle(ABAB);
        let mut tmp1 = tmp0.shuffle(BADC);
        // (X1, Y1, Z1, X1 + Y1)
        tmp0 = self.0.blend::<D_LANES>(tmp0.add(tmp1));
        // (S1, S2, S3, -S4) = (X1^2, Y1^2, Z1^2, -(X1 + Y1)^2)
        tmp1 = tmp0.square_and_negate_d();

        let zero = Fe4(ZERO);
        let s1 = tmp1.shuffle(AAAA);
        let s2 = tmp1.shuffle(BBBB);

        // (0, 0, 2 S3, -S4) + (S1, S1, S1, S1) + (S2, 0, 0, S2) + (0, -S2, -S2, 0)
        tmp0 = zero.blend::<C_LANES>(tmp1.add(tmp1));
        tmp0 = tmp0.blend::<D_LANES>(tmp1);
        tmp0 = tmp0.add(s1);
        tmp0 = tmp0.add(zero.blend::<AD_LANES>(s2));
        tmp0 = tmp0.add(zero.blend::<BC_LANES>(s2.negate_lazy()));

        tmp1 = tmp0.shuffle(DBBD);
        tmp0 = tmp0.shuffle(CACA);
        Self(tmp0.mul(&tmp1))
    }

    #[target_feature(enable = "avx,avx2")]
    fn add(&self, other: &Cached) -> Self {
        let mut tmp = self.0;
        // (Y1 - X1, Y1 + X1, Z1, T1)
        tmp = tmp.blend::<AB_LANES>(tmp.diff_sum());
        // (S8, S9, S10, S11)
        tmp = tmp.mul(&other.0);
        // (S8, S9, S11, S10)
        tmp = tmp.shuffle(ABDC);
        // (S9 - S8, S9 + S8, S10 - S11, S10 + S11)
        tmp = tmp.diff_sum();
        let t0 = tmp.shuffle(ADDA);
        let t1 = tmp.shuffle(CBCB);
        Self(t0.mul(&t1))
    }
}

impl Cached {
    #[target_feature(enable = "avx,avx2")]
    fn from(p: Extended) -> Self {
        let mut x = p.0;
        x = x.blend::<AB_LANES>(x.diff_sum());
        // The curve's d is -121665/121666, so 2d's numerator and denominator
        // scale the lanes in place of a multiplication by d.
        x = x.mul_small(121666, 121666, 2 * 121666, 2 * 121665);
        x = x.blend::<D_LANES>(x.neg());
        Self(x)
    }

    #[target_feature(enable = "avx,avx2")]
    fn neg(&self) -> Self {
        let swapped = self.0.shuffle(BACD);
        Self(swapped.blend::<D_LANES>(swapped.negate_lazy()))
    }
}

/// Four field elements; see the module documentation.
#[derive(Clone, Copy)]
struct Fe4([__m256i; 5]);

/// Lane selections for [`Fe4::blend`], over each vector's 32-bit lanes.
const A_LANES: i32 = 0b0000_0101;
const B_LANES: i32 = 0b0000_1010;
const C_LANES: i32 = 0b0101_0000;
const D_LANES: i32 = 0b1010_0000;
const AB_LANES: i32 = A_LANES | B_LANES;
const AD_LANES: i32 = A_LANES | D_LANES;
const BC_LANES: i32 = B_LANES | C_LANES;

/// `D_LANES` over the 64-bit lanes of a product.
const D_LANES64: i32 = 0b11_00_00_00;

/// Permutations for [`Fe4::shuffle`], named by what each turns `(A, B, C, D)` into.
const AAAA: [i32; 8] = [0, 0, 2, 2, 0, 0, 2, 2];
const BBBB: [i32; 8] = [1, 1, 3, 3, 1, 1, 3, 3];
const CACA: [i32; 8] = [4, 0, 6, 2, 4, 0, 6, 2];
const DBBD: [i32; 8] = [5, 1, 7, 3, 1, 5, 3, 7];
const ADDA: [i32; 8] = [0, 5, 2, 7, 5, 0, 7, 2];
const CBCB: [i32; 8] = [4, 1, 6, 3, 4, 1, 6, 3];
const ABAB: [i32; 8] = [0, 1, 2, 3, 0, 1, 2, 3];
const BADC: [i32; 8] = [1, 0, 3, 2, 5, 4, 7, 6];
const BACD: [i32; 8] = [1, 0, 3, 2, 4, 5, 6, 7];
const ABDC: [i32; 8] = [0, 1, 2, 3, 5, 4, 7, 6];

/// Reinterprets eight 32-bit lanes as a vector, in a constant.
const fn v(x: [u32; 8]) -> __m256i {
    // SAFETY: both are 32 bytes, and every bit pattern is a valid __m256i
    unsafe { core::mem::transmute(x) }
}

const ZERO: [__m256i; 5] = [v([0; 8]); 5];

/// The identity as a [`Cached`] point: `(Y - X, Y + X, 2Z, 2dT)` scaled by
/// 121666 is `(121666, 121666, 2 * 121666, 0)`.
const CACHED_IDENTITY: [__m256i; 5] = [
    v([121666, 121666, 0, 0, 2 * 121666, 0, 0, 0]),
    v([0; 8]),
    v([0; 8]),
    v([0; 8]),
    v([0; 8]),
];

/// `(0, 1, 1, 0)`, the identity.
const EXTENDED_IDENTITY: [__m256i; 5] = [
    v([0, 1, 0, 0, 1, 0, 0, 0]),
    v([0; 8]),
    v([0; 8]),
    v([0; 8]),
    v([0; 8]),
];

/// The limbs of `2p` in each lane: the first vector's, then the others'.
const P_TIMES_2_LO: __m256i = v([
    67108845 << 1,
    67108845 << 1,
    33554431 << 1,
    33554431 << 1,
    67108845 << 1,
    67108845 << 1,
    33554431 << 1,
    33554431 << 1,
]);
const P_TIMES_2_HI: __m256i = v([
    67108863 << 1,
    67108863 << 1,
    33554431 << 1,
    33554431 << 1,
    67108863 << 1,
    67108863 << 1,
    33554431 << 1,
    33554431 << 1,
]);

/// The limbs of `16p` in each lane: the first vector's, then the others'.
const P_TIMES_16_LO: __m256i = v([
    67108845 << 4,
    67108845 << 4,
    33554431 << 4,
    33554431 << 4,
    67108845 << 4,
    67108845 << 4,
    33554431 << 4,
    33554431 << 4,
]);
const P_TIMES_16_HI: __m256i = v([
    67108863 << 4,
    67108863 << 4,
    33554431 << 4,
    33554431 << 4,
    67108863 << 4,
    67108863 << 4,
    33554431 << 4,
    33554431 << 4,
]);

/// Each limb's bit offset within a field element, alternately 26 and 25 bits wide.
const LIMB_OFFSETS: [u32; 10] = [0, 26, 51, 77, 102, 128, 153, 179, 204, 230];

impl Fe4 {
    /// Packs four field elements below 2^255.
    #[target_feature(enable = "avx,avx2")]
    fn new(x: &[[u64; 4]; 4]) -> Self {
        let limb = |x: &[u64; 4], i: usize| -> i32 {
            let (offset, bits) = (LIMB_OFFSETS[i], 26 - (i as u32 & 1));
            let (word, shift) = ((offset / 64) as usize, offset % 64);
            let mut v = x[word] >> shift;
            if shift + bits > 64 {
                v |= x[word + 1] << (64 - shift);
            }
            (v & ((1 << bits) - 1)) as i32
        };

        let mut out = ZERO;
        for (i, out) in out.iter_mut().enumerate() {
            let (lo, hi) = (2 * i, 2 * i + 1);
            *out = _mm256_setr_epi32(
                limb(&x[0], lo),
                limb(&x[1], lo),
                limb(&x[0], hi),
                limb(&x[1], hi),
                limb(&x[2], lo),
                limb(&x[3], lo),
                limb(&x[2], hi),
                limb(&x[3], hi),
            );
        }
        Self(out)
    }

    /// Unpacks the four field elements, each reduced.
    #[target_feature(enable = "avx,avx2")]
    fn split(&self) -> [[u64; 4]; 4] {
        let mut lanes = [[0u32; 8]; 5];
        for (lanes, v) in lanes.iter_mut().zip(self.0) {
            // SAFETY: `lanes` is 32 writable bytes
            unsafe { _mm256_storeu_si256(lanes.as_mut_ptr().cast(), v) };
        }

        // Each lane's radix 2^51 limbs, as in dalek's `split`.
        // Wrapping, so a debug build's overflow checks don't branch on the
        // secret limbs; none of these overflows.
        let mut out = [[0u64; 5]; 4];
        for (i, l) in lanes.iter().enumerate() {
            let l = l.map(u64::from);
            out[0][i] = l[0].wrapping_add(l[2] << 26);
            out[1][i] = l[1].wrapping_add(l[3] << 26);
            out[2][i] = l[4].wrapping_add(l[6] << 26);
            out[3][i] = l[5].wrapping_add(l[7] << 26);
        }

        out.map(|mut l| {
            // dalek's `reduce` then `to_bytes`: a weak carry leaves each
            // limb below 2^51 + 2^13, `q` is 1 exactly when the value is at
            // least p, and adding 19q then carrying and dropping 2^255
            // subtracts it, leaving every limb below 2^51.
            const MASK: u64 = (1 << 51) - 1;
            let c = l.map(|l| l >> 51);
            for l in &mut l {
                *l &= MASK;
            }
            l[0] = l[0].wrapping_add(c[4].wrapping_mul(19));
            for i in 1..5 {
                l[i] = l[i].wrapping_add(c[i - 1]);
            }

            let mut q = l[0].wrapping_add(19) >> 51;
            for l in &l[1..] {
                q = l.wrapping_add(q) >> 51;
            }
            l[0] = l[0].wrapping_add(q.wrapping_mul(19));
            for i in 0..4 {
                l[i + 1] = l[i + 1].wrapping_add(l[i] >> 51);
                l[i] &= MASK;
            }
            l[4] &= MASK;

            [
                l[0] | (l[1] << 51),
                (l[1] >> 13) | (l[2] << 38),
                (l[2] >> 26) | (l[3] << 25),
                (l[3] >> 39) | (l[4] << 12),
            ]
        })
    }

    #[target_feature(enable = "avx,avx2")]
    fn shuffle(&self, control: [i32; 8]) -> Self {
        let c = _mm256_setr_epi32(
            control[0], control[1], control[2], control[3], control[4], control[5], control[6],
            control[7],
        );
        Self(self.0.map(|x| _mm256_permutevar8x32_epi32(x, c)))
    }

    /// Takes the lanes `LANES` selects from `other`.
    #[target_feature(enable = "avx,avx2")]
    fn blend<const LANES: i32>(&self, other: Self) -> Self {
        let mut out = self.0;
        for (out, other) in out.iter_mut().zip(other.0) {
            *out = _mm256_blend_epi32::<LANES>(*out, other);
        }
        Self(out)
    }

    /// Adds without reducing.
    #[target_feature(enable = "avx,avx2")]
    fn add(&self, other: Self) -> Self {
        let mut out = self.0;
        for (out, other) in out.iter_mut().zip(other.0) {
            *out = _mm256_add_epi32(*out, other);
        }
        Self(out)
    }

    /// Negates by subtracting from `2p`, without reducing.
    #[target_feature(enable = "avx,avx2")]
    fn negate_lazy(&self) -> Self {
        Self([
            _mm256_sub_epi32(P_TIMES_2_LO, self.0[0]),
            _mm256_sub_epi32(P_TIMES_2_HI, self.0[1]),
            _mm256_sub_epi32(P_TIMES_2_HI, self.0[2]),
            _mm256_sub_epi32(P_TIMES_2_HI, self.0[3]),
            _mm256_sub_epi32(P_TIMES_2_HI, self.0[4]),
        ])
    }

    /// Negates by subtracting from `16p`, then reduces.
    #[target_feature(enable = "avx,avx2")]
    fn neg(&self) -> Self {
        Self([
            _mm256_sub_epi32(P_TIMES_16_LO, self.0[0]),
            _mm256_sub_epi32(P_TIMES_16_HI, self.0[1]),
            _mm256_sub_epi32(P_TIMES_16_HI, self.0[2]),
            _mm256_sub_epi32(P_TIMES_16_HI, self.0[3]),
            _mm256_sub_epi32(P_TIMES_16_HI, self.0[4]),
        ])
        .reduce()
    }

    /// Given `(A, B, C, D)`, computes `(B - A, B + A, D - C, D + C)`.
    #[target_feature(enable = "avx,avx2")]
    fn diff_sum(&self) -> Self {
        let tmp1 = self.shuffle(BADC);
        let tmp2 = self.blend::<{ A_LANES | C_LANES }>(self.negate_lazy());
        tmp1.add(tmp2)
    }

    /// Carries each limb into the next once, folding the top carry back by 19.
    #[target_feature(enable = "avx,avx2")]
    fn reduce(&self) -> Self {
        let shifts = _mm256_setr_epi32(26, 26, 25, 25, 26, 26, 25, 25);
        let masks = _mm256_setr_epi32(
            (1 << 26) - 1,
            (1 << 26) - 1,
            (1 << 25) - 1,
            (1 << 25) - 1,
            (1 << 26) - 1,
            (1 << 26) - 1,
            (1 << 25) - 1,
            (1 << 25) - 1,
        );

        // Each limb's carry, moved to the lane of the limb it carries into.
        let rotated_carryout =
            |v: __m256i| _mm256_shuffle_epi32::<0b01_00_11_10>(_mm256_srlv_epi32(v, shifts));
        // The low limbs' lanes from `lo`, the high limbs' from `hi`.
        let combine = |lo: __m256i, hi: __m256i| _mm256_blend_epi32::<0b11_00_11_00>(lo, hi);

        let mut v = self.0;

        let c10 = rotated_carryout(v[0]);
        v[0] = _mm256_add_epi32(
            _mm256_and_si256(v[0], masks),
            combine(_mm256_setzero_si256(), c10),
        );

        let c32 = rotated_carryout(v[1]);
        v[1] = _mm256_add_epi32(_mm256_and_si256(v[1], masks), combine(c10, c32));

        let c54 = rotated_carryout(v[2]);
        v[2] = _mm256_add_epi32(_mm256_and_si256(v[2], masks), combine(c32, c54));

        let c76 = rotated_carryout(v[3]);
        v[3] = _mm256_add_epi32(_mm256_and_si256(v[3], masks), combine(c54, c76));

        let c98 = rotated_carryout(v[4]);
        v[4] = _mm256_add_epi32(_mm256_and_si256(v[4], masks), combine(c76, c98));

        // c98 holds (c9, c9) in each lane pair's high limb; spread c9 into
        // 64-bit lanes, multiply by 19, and move it back to the low limbs.
        let c9_spread = _mm256_shuffle_epi32::<0b11_01_10_00>(c98);
        let c9_19_spread = _mm256_mul_epu32(c9_spread, _mm256_set1_epi64x(19));
        let c9_19 = _mm256_shuffle_epi32::<0b11_01_10_00>(c9_19_spread);

        v[0] = _mm256_add_epi32(v[0], c9_19);

        Self(v)
    }

    /// Reduces ten 64-bit lanes of products to a `Fe4`.
    #[target_feature(enable = "avx,avx2")]
    fn reduce64(mut z: [__m256i; 10]) -> Self {
        let low_25_bits = _mm256_set1_epi64x((1 << 25) - 1);
        let low_26_bits = _mm256_set1_epi64x((1 << 26) - 1);

        let carry = |z: &mut [__m256i; 10], i: usize| {
            if i.is_multiple_of(2) {
                z[i + 1] = _mm256_add_epi64(z[i + 1], _mm256_srli_epi64::<26>(z[i]));
                z[i] = _mm256_and_si256(z[i], low_26_bits);
            } else {
                z[i + 1] = _mm256_add_epi64(z[i + 1], _mm256_srli_epi64::<25>(z[i]));
                z[i] = _mm256_and_si256(z[i], low_25_bits);
            }
        };

        // Two interleaved carry chains, 0..4 and 4..9.
        carry(&mut z, 0);
        carry(&mut z, 4);
        carry(&mut z, 1);
        carry(&mut z, 5);
        carry(&mut z, 2);
        carry(&mut z, 6);
        carry(&mut z, 3);
        carry(&mut z, 7);
        carry(&mut z, 4);
        carry(&mut z, 8);

        // z9's carry c is below 2^39, too large to multiply by 19 in one
        // 32-bit product, so it splits at bit 26 and folds into z0 and z1.
        let c = _mm256_srli_epi64::<25>(z[9]);
        z[9] = _mm256_and_si256(z[9], low_25_bits);
        let x19 = _mm256_set1_epi64x(19);
        let c0 = _mm256_mul_epu32(_mm256_and_si256(c, low_26_bits), x19);
        let c1 = _mm256_mul_epu32(_mm256_srli_epi64::<26>(c), x19);

        z[0] = _mm256_add_epi64(z[0], c0);
        z[1] = _mm256_add_epi64(z[1], c1);
        carry(&mut z, 0);

        // Repacks (a0, 0, b0, 0, c0, 0, d0, 0) and (a1, 0, b1, 0, ...) into
        // (a0, b0, a1, b1, c0, d0, c1, d1).
        let repack_pair = |x: __m256i, y: __m256i| {
            let x = _mm256_shuffle_epi32::<0b11_01_10_00>(x);
            let y = _mm256_shuffle_epi32::<0b10_00_11_01>(y);
            _mm256_blend_epi32::<0b11001100>(x, y)
        };

        Self([
            repack_pair(z[0], z[1]),
            repack_pair(z[2], z[3]),
            repack_pair(z[4], z[5]),
            repack_pair(z[6], z[7]),
            repack_pair(z[8], z[9]),
        ])
    }

    /// Splits `self` into its ten limbs, each in the low half of a 64-bit lane.
    #[target_feature(enable = "avx,avx2")]
    fn unpack(&self) -> [__m256i; 10] {
        let zero = _mm256_setzero_si256();
        let mut out = [zero; 10];
        for (i, v) in self.0.iter().enumerate() {
            out[2 * i] = _mm256_unpacklo_epi32(*v, zero);
            out[2 * i + 1] = _mm256_unpackhi_epi32(*v, zero);
        }
        out
    }

    /// Multiplies lanes A, B, C, and D by small constants.
    #[target_feature(enable = "avx,avx2")]
    fn mul_small(&self, a: i32, b: i32, c: i32, d: i32) -> Self {
        let consts = _mm256_setr_epi32(a, 0, b, 0, c, 0, d, 0);
        Self::reduce64(self.unpack().map(|x| _mm256_mul_epu32(x, consts)))
    }

    /// Squares each lane, then negates lane D.
    #[target_feature(enable = "avx,avx2")]
    fn square_and_negate_d(&self) -> Self {
        let m = |x, y| _mm256_mul_epu32(x, y);
        let add = |x, y| _mm256_add_epi64(x, y);
        let dbl = |x| _mm256_slli_epi64::<1>(x);
        let v19 = _mm256_set1_epi64x(19);

        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] = self.unpack();

        let x0_2 = _mm256_slli_epi32::<1>(x0);
        let x1_2 = _mm256_slli_epi32::<1>(x1);
        let x2_2 = _mm256_slli_epi32::<1>(x2);
        let x3_2 = _mm256_slli_epi32::<1>(x3);
        let x4_2 = _mm256_slli_epi32::<1>(x4);
        let x5_2 = _mm256_slli_epi32::<1>(x5);
        let x6_2 = _mm256_slli_epi32::<1>(x6);
        let x7_2 = _mm256_slli_epi32::<1>(x7);

        let x5_19 = m(v19, x5);
        let x6_19 = m(v19, x6);
        let x7_19 = m(v19, x7);
        let x8_19 = m(v19, x8);
        let x9_19 = m(v19, x9);

        let sum = |terms: &[__m256i]| terms.iter().copied().reduce(add).unwrap();

        let z0 = sum(&[
            m(x0, x0),
            m(x2_2, x8_19),
            m(x4_2, x6_19),
            dbl(sum(&[m(x1_2, x9_19), m(x3_2, x7_19), m(x5, x5_19)])),
        ]);
        let z1 = sum(&[
            m(x0_2, x1),
            m(x3_2, x8_19),
            m(x5_2, x6_19),
            dbl(sum(&[m(x2, x9_19), m(x4, x7_19)])),
        ]);
        let z2 = sum(&[
            m(x0_2, x2),
            m(x1_2, x1),
            m(x4_2, x8_19),
            m(x6, x6_19),
            dbl(sum(&[m(x3_2, x9_19), m(x5_2, x7_19)])),
        ]);
        let z3 = sum(&[
            m(x0_2, x3),
            m(x1_2, x2),
            m(x5_2, x8_19),
            dbl(sum(&[m(x4, x9_19), m(x6, x7_19)])),
        ]);
        let z4 = sum(&[
            m(x0_2, x4),
            m(x1_2, x3_2),
            m(x2, x2),
            m(x6_2, x8_19),
            dbl(sum(&[m(x5_2, x9_19), m(x7, x7_19)])),
        ]);
        let z5 = sum(&[
            m(x0_2, x5),
            m(x1_2, x4),
            m(x2_2, x3),
            m(x7_2, x8_19),
            dbl(m(x6, x9_19)),
        ]);
        let z6 = sum(&[
            m(x0_2, x6),
            m(x1_2, x5_2),
            m(x2_2, x4),
            m(x3_2, x3),
            m(x8, x8_19),
            dbl(m(x7_2, x9_19)),
        ]);
        let z7 = sum(&[
            m(x0_2, x7),
            m(x1_2, x6),
            m(x2_2, x5),
            m(x3_2, x4),
            dbl(m(x8, x9_19)),
        ]);
        let z8 = sum(&[
            m(x0_2, x8),
            m(x1_2, x7_2),
            m(x2_2, x6),
            m(x3_2, x5_2),
            m(x4, x4),
            dbl(m(x9, x9_19)),
        ]);
        let z9 = sum(&[
            m(x0_2, x9),
            m(x1_2, x8),
            m(x2_2, x7),
            m(x3_2, x6),
            m(x4_2, x5),
        ]);

        // Negates lane D by subtracting it from 2^37 p, whose limbs, each
        // shifted by 37, exceed every product sum.
        let low_p37 = _mm256_set1_epi64x(0x3ffffed << 37);
        let even_p37 = _mm256_set1_epi64x(0x3ffffff << 37);
        let odd_p37 = _mm256_set1_epi64x(0x1ffffff << 37);
        let negate_d = |x, p| _mm256_blend_epi32::<D_LANES64>(x, _mm256_sub_epi64(p, x));

        Self::reduce64([
            negate_d(z0, low_p37),
            negate_d(z1, odd_p37),
            negate_d(z2, even_p37),
            negate_d(z3, odd_p37),
            negate_d(z4, even_p37),
            negate_d(z5, odd_p37),
            negate_d(z6, even_p37),
            negate_d(z7, odd_p37),
            negate_d(z8, even_p37),
            negate_d(z9, odd_p37),
        ])
    }

    /// Multiplies lane by lane.
    #[rustfmt::skip]
    #[target_feature(enable = "avx,avx2")]
    fn mul(&self, rhs: &Self) -> Self {
        let m = |x, y| _mm256_mul_epu32(x, y);
        let v19 = _mm256_set1_epi64x(19);

        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] = self.unpack();
        let [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9] = rhs.unpack();

        let y1_19 = m(v19, y1);
        let y2_19 = m(v19, y2);
        let y3_19 = m(v19, y3);
        let y4_19 = m(v19, y4);
        let y5_19 = m(v19, y5);
        let y6_19 = m(v19, y6);
        let y7_19 = m(v19, y7);
        let y8_19 = m(v19, y8);
        let y9_19 = m(v19, y9);

        let x1_2 = _mm256_add_epi32(x1, x1);
        let x3_2 = _mm256_add_epi32(x3, x3);
        let x5_2 = _mm256_add_epi32(x5, x5);
        let x7_2 = _mm256_add_epi32(x7, x7);
        let x9_2 = _mm256_add_epi32(x9, x9);

        let sum = |terms: [__m256i; 10]| terms.into_iter().reduce(|x, y| _mm256_add_epi64(x, y)).unwrap();

        Self::reduce64([
            sum([m(x0, y0), m(x1_2, y9_19), m(x2, y8_19), m(x3_2, y7_19), m(x4, y6_19), m(x5_2, y5_19), m(x6, y4_19), m(x7_2, y3_19), m(x8, y2_19), m(x9_2, y1_19)]),
            sum([m(x0, y1), m(x1, y0), m(x2, y9_19), m(x3, y8_19), m(x4, y7_19), m(x5, y6_19), m(x6, y5_19), m(x7, y4_19), m(x8, y3_19), m(x9, y2_19)]),
            sum([m(x0, y2), m(x1_2, y1), m(x2, y0), m(x3_2, y9_19), m(x4, y8_19), m(x5_2, y7_19), m(x6, y6_19), m(x7_2, y5_19), m(x8, y4_19), m(x9_2, y3_19)]),
            sum([m(x0, y3), m(x1, y2), m(x2, y1), m(x3, y0), m(x4, y9_19), m(x5, y8_19), m(x6, y7_19), m(x7, y6_19), m(x8, y5_19), m(x9, y4_19)]),
            sum([m(x0, y4), m(x1_2, y3), m(x2, y2), m(x3_2, y1), m(x4, y0), m(x5_2, y9_19), m(x6, y8_19), m(x7_2, y7_19), m(x8, y6_19), m(x9_2, y5_19)]),
            sum([m(x0, y5), m(x1, y4), m(x2, y3), m(x3, y2), m(x4, y1), m(x5, y0), m(x6, y9_19), m(x7, y8_19), m(x8, y7_19), m(x9, y6_19)]),
            sum([m(x0, y6), m(x1_2, y5), m(x2, y4), m(x3_2, y3), m(x4, y2), m(x5_2, y1), m(x6, y0), m(x7_2, y9_19), m(x8, y8_19), m(x9_2, y7_19)]),
            sum([m(x0, y7), m(x1, y6), m(x2, y5), m(x3, y4), m(x4, y3), m(x5, y2), m(x6, y1), m(x7, y0), m(x8, y9_19), m(x9, y8_19)]),
            sum([m(x0, y8), m(x1_2, y7), m(x2, y6), m(x3_2, y5), m(x4, y4), m(x5_2, y3), m(x6, y2), m(x7_2, y1), m(x8, y0), m(x9_2, y9_19)]),
            sum([m(x0, y9), m(x1, y8), m(x2, y7), m(x3, y6), m(x4, y5), m(x5, y4), m(x6, y3), m(x7, y2), m(x8, y1), m(x9, y0)]),
        ])
    }
}

/// `[B, 3B, 5B, ..., 127B]` as [`Cached`] points, B the base point.
static BASE_ODD_MULTIPLES: [[__m256i; 5]; 64] = {
    let mut out = [ZERO; 64];
    let mut i = 0;
    while i < 64 {
        let mut j = 0;
        while j < 5 {
            out[i][j] = v(BASE_ODD_MULTIPLES_LIMBS[i][j]);
            j += 1;
        }
        i += 1;
    }
    out
};

/// `[B', 3B', 5B', ..., 127B']` as [`Cached`] points, for `B' = [2^128]B`.
static BASE128_ODD_MULTIPLES: [[__m256i; 5]; 64] = {
    let mut out = [ZERO; 64];
    let mut i = 0;
    while i < 64 {
        let mut j = 0;
        while j < 5 {
            out[i][j] = v(BASE128_ODD_MULTIPLES_LIMBS[i][j]);
            j += 1;
        }
        i += 1;
    }
    out
};

#[rustfmt::skip]
const BASE_ODD_MULTIPLES_LIMBS: [[[u32; 8]; 5]; 64] = [
    [
        [3571425, 10045002, 19036563, 1096096, 243332, 65897020, 0, 28963681],
        [30896895, 63055514, 1614915, 5095970, 0, 53791688, 0, 31258312],
        [13347627, 40339464, 2236269, 11185503, 0, 22520087, 0, 8659512],
        [11125413, 29139905, 32037254, 28360723, 0, 64556417, 0, 9635759],
        [33268144, 47262491, 4336918, 15795740, 0, 22027545, 0, 4846528],
    ],
    [
        [47099681, 31447946, 29365447, 24740513, 42991046, 18317844, 16051644, 21404226],
        [31708133, 28909527, 2366091, 13703791, 469246, 54159622, 2601402, 32988002],
        [63432457, 30251794, 15163516, 18491340, 28144087, 35605455, 13682295, 18474872],
        [12221607, 4967598, 26061980, 26008006, 20226147, 9726961, 17410, 18051083],
        [60569645, 62487085, 11911242, 21920922, 4092105, 38186967, 22431483, 31366585],
    ],
    [
        [18147205, 62587998, 2554617, 536692, 11924528, 26674131, 17645433, 24341419],
        [11573357, 27579485, 31491870, 29000885, 10800976, 51902791, 28076395, 20464029],
        [56031649, 10856669, 11791193, 26769430, 25306956, 5922200, 6630685, 9385098],
        [31319348, 23906711, 16290213, 32142166, 61106354, 17181823, 3548308, 12022566],
        [5904298, 50218605, 11826440, 5492249, 10379071, 3472255, 172742, 31948344],
    ],
    [
        [10625852, 15193821, 22918394, 23676410, 53695416, 54987793, 10067515, 11747680],
        [65013325, 1309652, 29616320, 28922974, 60360891, 19621771, 9938982, 30406429],
        [54967954, 65931918, 5595602, 25719523, 64909864, 30566415, 15945272, 8495317],
        [1167157, 55265018, 11507029, 31641054, 43497904, 2367338, 12937761, 27517066],
        [656704, 2544994, 13006713, 480979, 38471594, 62541240, 25353597, 11531760],
    ],
    [
        [22176662, 3984313, 27495285, 4110608, 2909584, 30594106, 15677919, 2549183],
        [33979105, 62269905, 2071511, 6894756, 53189950, 47232857, 6408191, 6123225],
        [32553873, 63948030, 12612401, 3633166, 24054373, 37626618, 14481327, 8520484],
        [56552486, 10749438, 12034813, 28811946, 1445640, 36755601, 12104575, 10257833],
        [22795808, 48761311, 1136056, 9380768, 1411523, 5341811, 27318329, 9686767],
    ],
    [
        [21157200, 39156966, 20473176, 4934657, 61478183, 45121537, 5429856, 13035023],
        [7954529, 58789246, 31440083, 7054221, 38438565, 36856107, 1364112, 14548122],
        [26120083, 36321360, 4919997, 31687496, 33757765, 36237559, 15243054, 32163861],
        [25878307, 46544824, 19455951, 2414935, 16844726, 56521560, 32680554, 26660660],
        [48360220, 43407178, 12187042, 24925816, 7423722, 25746484, 12814654, 17395963],
    ],
    [
        [63153652, 32195955, 4087908, 8431689, 30392384, 47203165, 8986649, 9053039],
        [63659241, 47988767, 2931872, 19953600, 11747107, 51610101, 20952181, 13364887],
        [3659197, 58790649, 5930099, 2605312, 28477896, 580728, 20579735, 2610622],
        [41781607, 17161358, 10690531, 24368015, 47027031, 36742339, 5414694, 13156365],
        [13237853, 51182423, 8954802, 29006542, 22643989, 56896541, 22830593, 10289708],
    ],
    [
        [1401265, 58846825, 30911620, 32239180, 15391552, 15200821, 6339309, 16403588],
        [55913797, 29541724, 1664461, 21709410, 38470488, 47097092, 17674945, 32666066],
        [22844482, 10797709, 27548106, 31638735, 34500968, 26611503, 19727211, 13160873],
        [31485204, 14496164, 13981208, 10276888, 5748808, 35024436, 2740987, 7479021],
        [58541207, 14866135, 32344041, 545930, 62661488, 6941250, 27940205, 11976112],
    ],
    [
        [39849808, 44781685, 15697329, 24387845, 12501486, 50260092, 23199481, 31929024],
        [24823070, 27956017, 27034296, 10316465, 47664045, 11152446, 15719183, 30181617],
        [20771189, 19969144, 31433937, 19185213, 27565920, 10384445, 2893359, 9255362],
        [42894974, 11925545, 32134441, 32738810, 55916336, 32479272, 19563550, 5511385],
        [17857161, 47809169, 14564114, 27997751, 33024640, 38669671, 31956536, 27313245],
    ],
    [
        [58237774, 15917425, 18872208, 19394230, 17374297, 6101419, 4839741, 6596900],
        [66947393, 15744215, 18368993, 17750160, 41006525, 9205497, 2629667, 32170865],
        [66481381, 1919414, 28338762, 7372967, 33819153, 4156199, 27126309, 12739816],
        [44117158, 58545296, 22521371, 11809712, 28998792, 50731010, 30215699, 25748377],
        [23561284, 4160244, 9035405, 24895184, 39761639, 59253416, 8684759, 22487864],
    ],
    [
        [12671134, 56419053, 16092401, 30038207, 4002647, 47822606, 7151311, 28430768],
        [61041684, 35765374, 30598048, 19666539, 44150175, 40140037, 290469, 28442674],
        [18847796, 1371617, 33316881, 13199936, 43646578, 17068881, 12074900, 1537415],
        [10052225, 38316070, 27469797, 5297537, 50725570, 20435349, 10339121, 2779737],
        [18372189, 15466385, 24762130, 22217964, 23503887, 47844464, 10415034, 2606889],
    ],
    [
        [55082775, 45300503, 16032654, 5964396, 17743504, 24634761, 19493066, 5184611],
        [50172633, 35093294, 10040575, 23616256, 4543900, 61852191, 4049821, 7423669],
        [20295398, 40009376, 10487190, 15670429, 51972856, 58649552, 20436392, 3432497],
        [35189420, 54117751, 12825868, 6283038, 27540739, 30648758, 22658912, 9466689],
        [51737549, 40725785, 17409814, 25201086, 21156239, 34176168, 26814520, 5956424],
    ],
    [
        [8211442, 8014184, 6260823, 22108096, 32182620, 51844847, 2466270, 28582231],
        [27199739, 3848333, 31738017, 10892045, 4963982, 65391770, 32551997, 28906469],
        [16606846, 32207068, 26404535, 7614129, 45416902, 65584718, 13821785, 2646060],
        [36090634, 57981287, 32247670, 22837502, 31003861, 55448117, 6062915, 20369975],
        [27381403, 50578107, 522631, 29521058, 31137497, 40220737, 27628049, 1824195],
    ],
    [
        [59402443, 17056879, 29262689, 6131785, 52551472, 43367471, 29423199, 18899208],
        [5749414, 43514612, 11365899, 21514624, 65591890, 60945892, 19841732, 5628567],
        [19334369, 52500268, 12307673, 5267367, 3212103, 9035822, 29142161, 30520954],
        [57261330, 6819646, 22089161, 9800373, 55155453, 62250856, 13766735, 25244545],
        [54370226, 61888301, 24496089, 2540581, 65637506, 60274355, 18154273, 11687259],
    ],
    [
        [12521903, 26014045, 13995625, 33360175, 23605474, 7376434, 27229267, 17195036],
        [59482891, 10074423, 574357, 3857753, 61377787, 50306685, 5241065, 20234396],
        [23674717, 6997172, 20771841, 16858511, 40565304, 29973136, 7049812, 14585010],
        [1427477, 13295732, 31762066, 31499740, 60419925, 54666164, 22009424, 8089609],
        [58154031, 41593020, 15342328, 957047, 38937260, 37037498, 24871992, 32973409],
    ],
    [
        [30654745, 51286025, 21206982, 2433562, 12780105, 31732574, 33087964, 33081189],
        [66640017, 42720009, 16567620, 15300745, 1530367, 33001123, 20930247, 21042661],
        [15003356, 5294119, 22985605, 18928772, 32628461, 18230172, 14773298, 27193722],
        [27555, 65346287, 17017174, 7837720, 21499787, 42855613, 22474984, 13675085],
        [24164369, 50130116, 5973149, 24152073, 1577334, 25400030, 18648484, 32228854],
    ],
    [
        [49518649, 59119280, 31670678, 20396561, 61728330, 651402, 176032, 9529498],
        [61765532, 9082232, 32794568, 15526956, 48543100, 32614212, 19001206, 25680229],
        [32086091, 10373081, 8996131, 31822823, 35788988, 49973190, 30542040, 17858455],
        [48130197, 58121889, 27753291, 29923268, 54448075, 43300790, 9336565, 15770022],
        [57725546, 20557498, 9366233, 16023566, 16189031, 2837363, 24315301, 27003505],
    ],
    [
        [28286608, 10767548, 18220739, 5413236, 48253387, 58255702, 11864864, 28527159],
        [45038176, 58655197, 25648758, 10951484, 42564382, 34542843, 23146954, 22234334],
        [14858710, 24978793, 15040559, 4379220, 47621477, 40271440, 15650420, 1998736],
        [24106391, 9626149, 344505, 25253814, 34579800, 59687089, 25718289, 25904133],
        [1981195, 37751302, 26132048, 1764722, 13288231, 28808622, 12531301, 18292949],
    ],
    [
        [13869851, 31448904, 14963539, 7581293, 20536485, 35021083, 21257574, 33356609],
        [36903364, 18429241, 11097857, 5943856, 60583077, 40015815, 30509523, 31915271],
        [49161801, 40681915, 67892, 25454357, 22779677, 25798439, 15964829, 5863227],
        [60810637, 4496471, 5217137, 14095116, 50942411, 50712663, 2507380, 26844507],
        [34579752, 53519385, 10859797, 18816024, 42552864, 39478521, 6783896, 17277037],
    ],
    [
        [43287109, 27900723, 33182187, 2766754, 17041989, 1018260, 33392790, 4830032],
        [60194178, 30788903, 24728888, 14513195, 20897010, 28843233, 20111980, 17475240],
        [46042274, 19257042, 4628173, 31649727, 27388316, 66631493, 11541886, 6408028],
        [57024680, 49536568, 32050358, 31321917, 17437691, 49672356, 2884755, 20493991],
        [59553007, 46782643, 29001173, 1814088, 21930692, 51319706, 14965872, 30748046],
    ],
    [
        [16441817, 36111849, 6900424, 602234, 46522199, 16441484, 8135070, 21726541],
        [37711225, 32701959, 11679112, 13125533, 32154135, 9407918, 26554289, 620848],
        [19233407, 30086864, 14679568, 2797374, 4892806, 7993077, 247658, 5632804],
        [37427262, 26675495, 27125659, 13496131, 50718473, 40115609, 28505351, 27837393],
        [196819, 18410429, 7070012, 21691388, 29763371, 24754123, 9727048, 10930179],
    ],
    [
        [28319289, 40734650, 16225680, 24739184, 64272368, 35356897, 7866648, 13635853],
        [34165295, 48328447, 27041670, 23643655, 48949950, 52963288, 30411133, 6045174],
        [18583559, 41649834, 9813585, 26098520, 25682734, 26733526, 19276490, 10654728],
        [34867476, 52715968, 5694571, 13380978, 15134994, 1831255, 8608001, 17266401],
        [59925903, 44282172, 27802465, 1855069, 14234749, 36635487, 11302294, 10938429],
    ],
    [
        [8373273, 49064494, 4932071, 32997499, 38472880, 29335908, 14504412, 22460029],
        [31795930, 50785923, 25835990, 25790073, 65669841, 11360450, 9969157, 9008164],
        [50262498, 45869261, 16124434, 15336007, 882762, 42522623, 11277198, 26296377],
        [42332732, 59129236, 14452816, 567985, 208061, 34722729, 32008143, 14828749],
        [17937794, 36846032, 32102665, 4442466, 19745435, 31633451, 7146411, 15812027],
    ],
    [
        [30741269, 38648744, 12562645, 30092623, 25073992, 28730659, 27911745, 30000958],
        [2859794, 25991700, 17776078, 27091930, 2328322, 60061146, 18581824, 18039008],
        [58206333, 17917354, 1972306, 11853766, 2655376, 60543390, 18416710, 13287440],
        [62746330, 61423885, 21246577, 2266675, 60099139, 14804707, 14772234, 20679434],
        [26987698, 15488817, 715616, 2339565, 51980752, 17333865, 21965103, 10839820],
    ],
    [
        [18672548, 57660959, 16042910, 19519287, 62865851, 17580961, 26628347, 23774759],
        [368070, 3464471, 25888304, 30370559, 52396053, 45426828, 28745251, 9246829],
        [29090099, 57950037, 23104657, 4903923, 10987778, 56163684, 23621539, 10332760],
        [53338235, 44851161, 21606845, 31069622, 4243630, 34464392, 11286454, 5802022],
        [46710757, 63389067, 11642865, 1980986, 12967337, 28162061, 3854192, 30432268],
    ],
    [
        [12179834, 41005450, 12809619, 33525228, 4624405, 46957889, 16968743, 11827816],
        [51521162, 12466775, 31791271, 15303651, 49798465, 62714504, 6509600, 12918560],
        [20445559, 1756449, 28848701, 7920171, 9835040, 5900071, 28757409, 12376688],
        [18259496, 14281012, 21767026, 10232236, 20000226, 12400540, 4104902, 23570543],
        [3687440, 26546648, 13328821, 26841081, 49822734, 22334054, 244496, 24862543],
    ],
    [
        [59523541, 62195428, 3853227, 13954801, 12387708, 47627615, 27221350, 17899572],
        [63193587, 36343307, 14595132, 6880795, 1364792, 37648434, 3259017, 20536046],
        [30362834, 10440372, 9574624, 11729232, 63861613, 21748389, 5530846, 2721586],
        [18339760, 1550632, 17170271, 25732971, 28459263, 63142237, 21642345, 31557672],
        [10611282, 5204623, 18049257, 214175, 19432723, 49809070, 26010406, 27449522],
    ],
    [
        [19770733, 26478685, 9464541, 29158041, 28604307, 45196604, 7586524, 6641859],
        [65654484, 52230498, 30886612, 19112823, 47271809, 38942611, 16020035, 10773481],
        [27464323, 54451016, 20646645, 17732915, 23008717, 53626684, 3253189, 15614410],
        [52381752, 40693008, 7063024, 28469981, 51159478, 44543211, 19941777, 5985451],
        [13553668, 35524849, 14788737, 1883845, 12385775, 47958835, 29135466, 1776722],
    ],
    [
        [36719806, 20827965, 23175373, 32996806, 42041892, 65708790, 5467143, 20884008],
        [43256281, 40770646, 17244063, 31959819, 64366384, 43544617, 25057754, 12628720],
        [17337782, 58472057, 27906934, 15305274, 30292418, 39284317, 16946773, 24806712],
        [6485126, 32447403, 16261486, 13561940, 49439635, 10738368, 16419889, 8897231],
        [44812203, 40122262, 25496058, 2759794, 25295304, 52178368, 24154195, 29334408],
    ],
    [
        [42307254, 57217102, 1088936, 3832827, 33905401, 23130334, 6958056, 12622851],
        [3881189, 14870059, 19712830, 6071598, 38147944, 60776394, 3427938, 13765703],
        [7666911, 24227591, 17077136, 22967588, 6874639, 30915523, 11451695, 24292224],
        [13659529, 31984463, 28764736, 20506164, 64729627, 49321636, 28284636, 25472371],
        [39360308, 42281399, 9446504, 868960, 49227724, 21351115, 30561851, 11292096],
    ],
    [
        [7071115, 46444090, 5387916, 15432877, 27226682, 41506862, 2398278, 3978240],
        [51009614, 54216973, 24368938, 31392616, 38456150, 62313644, 6729154, 99724],
        [17474332, 62857913, 2619930, 30659308, 18268181, 32809239, 22826292, 24561895],
        [38187020, 67003092, 14118280, 16500577, 18808560, 64983716, 25712929, 32518261],
        [25735813, 62284262, 10824872, 20558596, 48149681, 31162667, 22608274, 26285185],
    ],
    [
        [963440, 63742255, 10230323, 25515008, 32506414, 6105697, 25980317, 24645129],
        [7162189, 8101249, 14679265, 33443386, 2002396, 8541405, 19442276, 4795881],
        [8116694, 51463069, 4415528, 25599140, 55805721, 39582709, 6719436, 30033839],
        [14468202, 42181869, 25188826, 9639755, 47546189, 62711146, 32762447, 18338064],
        [33880058, 32810909, 8969931, 13095238, 38360605, 40138517, 9246134, 4928058],
    ],
    [
        [63655588, 17883670, 9410246, 26162761, 5000571, 7349225, 23785252, 32751089],
        [28568737, 10733123, 9342397, 21570673, 54096560, 32467591, 20494687, 21511513],
        [47675157, 47932807, 29250946, 15672208, 59760469, 9945465, 14939287, 18437405],
        [37985267, 8609815, 31573002, 3373596, 47828883, 20834216, 13248616, 24154292],
        [5543543, 29553242, 3386453, 30501150, 25058089, 15236571, 8814395, 32462955],
    ],
    [
        [39158670, 15322548, 20495103, 3312736, 14557171, 12985179, 8044741, 3176899],
        [24673290, 29693310, 21412266, 18324699, 2154518, 40329021, 17500543, 3954277],
        [36758685, 38738957, 165513, 14691866, 3070475, 10424235, 17096536, 16896898],
        [59790459, 43094586, 8720681, 10423589, 1122030, 31545615, 4463786, 31811293],
        [49778992, 60881044, 20509974, 5832494, 64155961, 31483358, 4511231, 20307815],
    ],
    [
        [2863373, 40876242, 26865913, 24067353, 15726407, 40919070, 12953902, 9931535],
        [60934877, 42512204, 21649141, 21945190, 52211954, 60984193, 7046207, 5363493],
        [4205971, 64068464, 18197273, 7327176, 51527794, 21166920, 20669933, 11828242],
        [59782815, 49617225, 15379924, 457923, 9320508, 21498914, 3242540, 31563182],
        [27714753, 8664670, 3366162, 26338598, 56775518, 25796006, 13129151, 21388876],
    ],
    [
        [59276548, 49972346, 16795002, 33455915, 48430097, 53857205, 18627071, 32474471],
        [42160315, 50705892, 13530540, 28012698, 19833221, 55886870, 20191784, 9644313],
        [20372416, 28414713, 24084234, 31804096, 33815377, 36131001, 17251241, 18291088],
        [56234667, 14920441, 2033267, 29572003, 1724043, 45519699, 17873735, 501988],
        [50031659, 31517850, 15697583, 1016845, 43104661, 54769582, 8008601, 27257051],
    ],
    [
        [52951491, 66542164, 14853573, 30444631, 12045973, 24321813, 16545674, 18160646],
        [60107911, 1126003, 5947677, 19486116, 41119984, 30860440, 7935395, 13354438],
        [17841328, 11063269, 1664538, 26687568, 6268968, 22280371, 17275484, 4523163],
        [15886041, 56799482, 15446552, 21712778, 1005290, 17827215, 4978741, 6854882],
        [34319277, 47731002, 20321804, 28544575, 29591814, 63376351, 24754545, 26001714],
    ],
    [
        [66783087, 5234346, 46102, 8566476, 19947339, 20180418, 25398238, 3726678],
        [63890180, 46380965, 20674069, 5366544, 59661487, 48406612, 31533614, 7071217],
        [13104676, 1406631, 24326736, 19854367, 61039528, 11019904, 31967425, 19219275],
        [39003597, 30143957, 15351834, 8639435, 57309582, 61436794, 15830475, 10090318],
        [45923044, 6700175, 99413, 21263025, 23762647, 53905481, 6063914, 10065424],
    ],
    [
        [42822326, 57678669, 4052879, 25452667, 54049411, 2373092, 22337016, 7701046],
        [44382355, 43307377, 16761537, 30373573, 49790216, 23230748, 25655306, 10519391],
        [919475, 59371245, 1273450, 25558666, 9724711, 8556709, 25755845, 10887647],
        [25465699, 44651158, 17658392, 11257418, 29735193, 22885150, 7094716, 26828565],
        [48237389, 47661599, 27054393, 7328070, 27280193, 65616691, 23062005, 4170709],
    ],
    [
        [26535281, 60238317, 30343788, 25790743, 37993933, 24614372, 9523840, 10401918],
        [2783987, 29468958, 4697011, 19804475, 37246678, 46797720, 10261254, 18942252],
        [58135580, 60247753, 25301938, 6844561, 20949454, 39844754, 4552026, 919057],
        [6694071, 44126261, 32285330, 31370180, 24603698, 53328179, 13971149, 5325636],
        [64879487, 582094, 17982081, 19190425, 24951286, 26923842, 29077174, 33286062],
    ],
    [
        [54863941, 67016431, 1224043, 23371240, 62940074, 52101083, 13523637, 30366406],
        [36324581, 25407485, 18258623, 4698602, 50300544, 2658516, 26300935, 2611030],
        [27183975, 21791014, 18105064, 9875199, 58118912, 54198635, 6400311, 14767984],
        [33918318, 42937962, 14809334, 22136592, 10636588, 29082337, 29829692, 28549776],
        [61080905, 854212, 12202487, 20004503, 9256495, 6903981, 20567109, 347423],
    ],
    [
        [41391822, 34336880, 22362564, 14247996, 12115604, 41583344, 7639288, 28910945],
        [62066617, 59758859, 26665947, 11614812, 65737664, 45704543, 30324810, 12868376],
        [17491771, 43589814, 9454919, 26047850, 52629282, 39304244, 3868968, 19296062],
        [17826638, 30413590, 32534225, 32741469, 15012391, 14365713, 33039233, 14791399],
        [64115596, 59197067, 32739005, 23275744, 32954320, 22241406, 20788442, 4942942],
    ],
    [
        [31956192, 59570132, 2784352, 4237732, 47222312, 4860927, 18658867, 15279314],
        [63240583, 28160478, 23524941, 13390861, 66437406, 57718120, 33345312, 28896298],
        [39026193, 46239965, 21440243, 25070488, 64012383, 60999016, 16517060, 29565907],
        [18118181, 60161496, 4212092, 23976240, 36277753, 62363144, 5816868, 16964362],
        [18196138, 62490693, 281468, 7934713, 56027312, 62015725, 4837237, 32932252],
    ],
    [
        [29885826, 51028067, 30418143, 33438769, 62542283, 39442528, 31535876, 143299],
        [17143063, 56709783, 14451852, 15782104, 32762665, 14047066, 26295037, 5432487],
        [75151, 533606, 7539077, 30926189, 38410914, 23771680, 4872443, 29199566],
        [61522396, 48934708, 16223126, 207380, 11171993, 47975147, 14164574, 352966],
        [15449006, 56530757, 26796528, 12045834, 63738697, 40667227, 33001582, 9101885],
    ],
    [
        [43331297, 18431341, 25801195, 17267698, 19365485, 57295202, 22218985, 21284590],
        [2429849, 19152559, 10762172, 22564684, 21880390, 66866426, 20357935, 22641906],
        [19771185, 31652693, 3666117, 28136958, 23624283, 55101502, 6313920, 6783662],
        [3487137, 7092443, 11001876, 26196524, 47319246, 44542068, 17594073, 15027760],
        [49563607, 32191113, 4991283, 25400512, 46539152, 4155103, 32368171, 201203],
    ],
    [
        [20548943, 14334571, 4073874, 6368588, 53208883, 56484515, 15970071, 25561889],
        [49915097, 44030795, 11202344, 29284344, 60258023, 66225712, 8075764, 12383512],
        [45248912, 4933668, 9592153, 5819559, 31030983, 38174071, 32435814, 7442522],
        [62688129, 48218381, 22089545, 12897361, 21050881, 34278889, 7569163, 3225449],
        [19050183, 51089071, 32935757, 22640195, 66122318, 47144608, 18743677, 25177079],
    ],
    [
        [41186817, 46681702, 31819867, 32997133, 38559207, 27147015, 30293819, 16762988],
        [24154689, 51762873, 23883879, 13510519, 55338250, 61224161, 11663149, 30803960],
        [18104238, 14117824, 11724021, 21362053, 65704761, 35530242, 13498058, 33522849],
        [63812888, 23995539, 28920539, 24005193, 26412223, 36582218, 4251418, 26160309],
        [16822053, 66064082, 3482145, 31979593, 45937188, 54475379, 612917, 7976478],
    ],
    [
        [46509314, 55327128, 8944536, 274914, 26432930, 53829300, 21192572, 3569894],
        [20919764, 64356651, 30642344, 17215170, 20335124, 11203745, 18663316, 19024174],
        [59297055, 53842463, 3680204, 9806710, 54004169, 51484914, 29807998, 20134199],
        [14781592, 22628010, 26877930, 25880359, 30434803, 190607, 30184292, 8991040],
        [64400983, 64591751, 854562, 28216111, 20010398, 50414793, 9803872, 22687008],
    ],
    [
        [15091184, 32550863, 8818643, 4244752, 43123513, 64565526, 408838, 13206998],
        [16405061, 60379639, 31489017, 20949281, 27568751, 38734986, 8364264, 12451020],
        [16005217, 58008076, 1406778, 26546927, 39571784, 56365493, 31274296, 8918790],
        [23271122, 19453469, 27718201, 32742670, 234332, 36785342, 22601675, 14331046],
        [40636025, 22442705, 22115403, 23745859, 41164945, 61012, 12499614, 542137],
    ],
    [
        [62776018, 32835413, 17373246, 17187309, 54469193, 21770290, 15923753, 28996575],
        [59385210, 63082298, 12568449, 8509004, 9483342, 16105238, 5756054, 26890758],
        [53987996, 38201748, 5521661, 19060159, 18663191, 9093637, 27786835, 31189196],
        [65872678, 43635130, 27903055, 25020300, 65772737, 38110437, 5213502, 21909342],
        [4438979, 9680838, 10212446, 4764184, 13235684, 58245995, 20264570, 21024049],
    ],
    [
        [60835961, 48209103, 31049052, 4688268, 12426713, 59829045, 22302488, 29008521],
        [50401667, 29716596, 23531224, 7581281, 49071895, 6952617, 14934683, 8218256],
        [1601446, 36631413, 31774811, 29625330, 56786114, 8331539, 23129509, 19783344],
        [59514327, 64513110, 1772300, 5701338, 5737511, 16147555, 9461515, 5703271],
        [33072974, 54300426, 11940114, 1308663, 15627555, 4931627, 28443714, 20924342],
    ],
    [
        [18135013, 20358426, 4922557, 10015355, 65729669, 34786528, 26248549, 29194359],
        [797666, 34997544, 24316856, 25107230, 24612576, 4761401, 15307321, 32404252],
        [16501152, 60565831, 9487105, 9316022, 24986054, 31917592, 3962024, 2501883],
        [63356796, 50432342, 18044926, 30566881, 42032028, 31415202, 13524600, 16119907],
        [3927286, 57022374, 9265437, 21620772, 19481940, 3806938, 24836192, 14572399],
    ],
    [
        [10785787, 46564798, 368445, 33181384, 5319843, 52687136, 30347110, 29837357],
        [56436732, 47859251, 24141084, 22250712, 59046084, 4963427, 33463413, 17168859],
        [15512044, 6366740, 4737504, 27644548, 30307977, 25037929, 14593903, 12836490],
        [63878897, 34013023, 5860752, 7244096, 3689461, 57012135, 18389096, 11589351],
        [4682110, 36302830, 653422, 22316819, 14081831, 5657024, 11088376, 24110612],
    ],
    [
        [39907267, 45940262, 24887471, 18342609, 878445, 40456159, 12019082, 345107],
        [12794982, 28893944, 9447505, 11387200, 16961963, 13916996, 10893728, 25898006],
        [44934162, 53465865, 3583620, 1102334, 53917811, 63478576, 2426066, 10389549],
        [45096036, 37595344, 19367718, 20257175, 10280866, 41653449, 27665642, 375926],
        [45847901, 24064074, 32494820, 32204556, 10720704, 51079060, 1297436, 29853825],
    ],
    [
        [66303987, 36060363, 16494578, 24962147, 11971403, 49538586, 25060560, 1964341],
        [25988481, 27641502, 24909517, 27237087, 66646363, 52777626, 16360849, 10459972],
        [43930529, 34374176, 31225968, 8807030, 10394758, 35904854, 25325589, 19335583],
        [25094697, 34380951, 20051185, 32287161, 11739332, 53887441, 30517319, 26601892],
        [8868546, 35635502, 32513071, 28248087, 51946989, 14222744, 19198839, 23261841],
    ],
    [
        [51218008, 5070126, 11046681, 5320810, 61212079, 34104447, 23895089, 6460727],
        [39843528, 46278671, 10426120, 25624792, 66658766, 37140083, 28933107, 12969597],
        [59635793, 40220191, 5751421, 173680, 58321825, 740337, 1412847, 7682623],
        [975962, 56440763, 20812276, 22631115, 49095824, 19883130, 2419746, 31043648],
        [66208703, 39669328, 22525915, 3748897, 65994776, 34533552, 8126286, 18326047],
    ],
    [
        [64176557, 3912400, 19351673, 30068471, 31190055, 24221683, 33142424, 28698542],
        [34784792, 4109933, 3867193, 19557314, 2112512, 32715890, 24550117, 16595976],
        [35542761, 48024875, 10925431, 31526577, 66577735, 23189821, 13375709, 1735095],
        [59699254, 43854093, 29783239, 24777271, 19600372, 39924461, 2896720, 1472185],
        [56389656, 35980854, 33172342, 1370336, 23707480, 57654949, 7850973, 12655016],
    ],
    [
        [38372660, 57101970, 7044964, 12732710, 57535705, 6043201, 30858914, 10946592],
        [21023468, 6946992, 26403324, 23901823, 35695559, 23440687, 4763891, 6514074],
        [28662273, 30933699, 9352242, 26354829, 37402243, 3145176, 8770289, 525937],
        [54933102, 36695832, 3281859, 4755022, 23043294, 32794379, 15618886, 23602412],
        [9931565, 29897140, 2480737, 24193701, 7833615, 2284939, 893926, 13421882],
    ],
    [
        [22917795, 22088359, 28978099, 19794863, 60542318, 29878494, 31053731, 9080720],
        [23679072, 52547035, 28424916, 20647332, 4008761, 28267029, 12961289, 1589095],
        [55616194, 26678929, 14998265, 23274397, 54625466, 46244264, 28627706, 33030665],
        [11527330, 6449415, 26531607, 3472938, 41541592, 62607682, 19862690, 20564723],
        [32843805, 49066843, 28425824, 19521495, 48792073, 48242878, 27392443, 13175986],
    ],
    [
        [16185025, 61537525, 2961305, 1492442, 25123147, 3095034, 31896958, 33089615],
        [64748157, 18336595, 16522231, 25426312, 65718949, 35485695, 30554083, 10205918],
        [39626934, 39271045, 16420458, 9826240, 56483981, 27128085, 3783403, 13360006],
        [30793778, 66771960, 17241420, 6564573, 61102581, 29974476, 32385512, 9011754],
        [28068166, 11862220, 14323567, 12380617, 52090465, 16029056, 24495309, 21409233],
    ],
    [
        [59411973, 57437124, 11695483, 17586857, 16108987, 43449109, 31098002, 6248476],
        [42258047, 61595931, 29308533, 11742653, 43042345, 27373650, 30165249, 21929989],
        [49907221, 9620337, 21888081, 20981082, 56288861, 61562203, 33223566, 3582446],
        [57535017, 41003416, 22080416, 14463796, 65518565, 18127889, 24370863, 33332664],
        [66655380, 6430175, 471782, 11947673, 30596400, 18898659, 15930721, 4211851],
    ],
    [
        [6757410, 65455566, 13584784, 11362173, 10797127, 24451471, 19541370, 29309435],
        [40360156, 17685025, 18326181, 3846903, 13693365, 63049479, 31900359, 23385063],
        [52455038, 57513503, 22163311, 27095042, 48610726, 66454160, 12085341, 26357004],
        [22097042, 14063840, 6705778, 14342902, 66139825, 20702105, 31279090, 7495745],
        [27360710, 49314837, 18774847, 7146436, 37066216, 42004961, 22409916, 10524446],
    ],
    [
        [1497507, 33054449, 11839906, 2960428, 40538463, 18884538, 25018820, 4073970],
        [54484385, 43640735, 2808257, 20710708, 39840730, 27222424, 21783544, 11848522],
        [45765237, 48200555, 9299019, 9393151, 34818188, 56098995, 13575233, 21012731],
        [4265428, 49627650, 24960282, 9425650, 47883651, 2797524, 11853190, 22877329],
        [25008173, 64199503, 380047, 12107343, 12329448, 11914399, 764281, 29687002],
    ],
    [
        [35889734, 23047226, 4022841, 7017445, 7274086, 53316179, 25100176, 15310676],
        [42409427, 30270106, 6823853, 31551384, 40645017, 66489807, 18021817, 32669351],
        [39827134, 43680850, 28297996, 20258133, 26058742, 52643238, 22238331, 21690533],
        [60808002, 17499995, 30042246, 29310584, 48219954, 29389518, 8680514, 17844709],
        [6452896, 50116553, 9532047, 26821214, 44524351, 50428429, 21904953, 12608048],
    ],
];

#[rustfmt::skip]
const BASE128_ODD_MULTIPLES_LIMBS: [[[u32; 8]; 5]; 64] = [
    [
        [33425672, 7425143, 3374861, 28816419, 243332, 4103548, 0, 32678329],
        [17252508, 3835936, 20263116, 27730940, 0, 11987130, 0, 9492330],
        [33791402, 53542015, 11090609, 24160487, 0, 56067127, 0, 31067178],
        [29444476, 2332569, 23704984, 33295729, 0, 52162977, 0, 16201229],
        [49934628, 56916145, 1380430, 4415475, 0, 36769626, 0, 14491316],
    ],
    [
        [469030, 9893464, 10525819, 32388142, 30458580, 42266220, 18477543, 28009338],
        [62943746, 35432241, 25531409, 27370746, 37268794, 57585999, 4565811, 5043651],
        [11002397, 55849217, 29834871, 4511041, 22818467, 37830345, 15670009, 18539843],
        [7306546, 3864268, 18179915, 33154251, 16081533, 36906701, 21583978, 5951757],
        [7557255, 1547047, 2016169, 11134600, 58602796, 50962855, 22239466, 22033727],
    ],
    [
        [64916266, 41376789, 2240014, 32003051, 21701687, 56054222, 6660380, 29328983],
        [22231579, 13714381, 21807414, 10798512, 31836527, 29990178, 21087968, 19963754],
        [1132841, 45846232, 26662352, 22944854, 12387029, 19227848, 21298057, 6349477],
        [53099893, 54580637, 14615074, 23856655, 45629216, 36288, 352417, 4648192],
        [52334288, 28226047, 29189568, 3708856, 52316354, 8591520, 20611625, 26483113],
    ],
    [
        [9536423, 40223387, 18530526, 11435252, 59115431, 48319922, 28559777, 7760636],
        [63314706, 34429031, 25562180, 1426388, 28195385, 62602237, 13773326, 18890371],
        [49358777, 30765004, 20962801, 16282080, 16224531, 41142890, 13313366, 25408609],
        [21235644, 51931467, 27049593, 29900063, 59928024, 25739742, 30683313, 6934704],
        [61843093, 8524970, 1608843, 15301267, 45612222, 48319615, 28022226, 2326297],
    ],
    [
        [66619011, 3046671, 33547255, 10730213, 64897356, 15645100, 26297210, 11672043],
        [58255395, 10925798, 33060962, 10308608, 17844976, 49912602, 21437171, 31823509],
        [41102366, 5123752, 9636279, 1272323, 37659908, 39677598, 16295890, 2648281],
        [47981372, 60949429, 7794273, 15538764, 62858688, 54619614, 23224796, 4111311],
        [23088031, 6022706, 2133503, 8596444, 41408897, 54023797, 27663573, 32321070],
    ],
    [
        [33073881, 7745841, 17409311, 26640592, 13276419, 1857102, 27325068, 24853750],
        [17453018, 18115464, 31387978, 14068970, 34170188, 35473168, 17154383, 30953616],
        [16269118, 23123656, 3679971, 30246318, 682188, 26716347, 10608221, 31938794],
        [32848687, 27378012, 15618721, 22455293, 46576421, 37364197, 10891134, 31726493],
        [39659760, 14785102, 22343943, 10622874, 11139028, 30224413, 9524258, 22190707],
    ],
    [
        [40794965, 6450349, 17167239, 28594050, 43415135, 16839082, 3969859, 6351910],
        [42463671, 33937666, 8771971, 20164169, 8381907, 23705855, 2475289, 23563109],
        [36140249, 58634686, 6797025, 19904311, 45770597, 17908988, 16981864, 16237099],
        [66809438, 28423776, 3850096, 12398231, 23366119, 19794408, 33256942, 2902103],
        [12832886, 746106, 11071573, 18335348, 42286672, 64435925, 33040426, 31083483],
    ],
    [
        [63496272, 43658275, 31617640, 21202044, 51371632, 34507779, 18029421, 1734838],
        [20885610, 34803939, 332868, 563454, 62907605, 26605590, 26374785, 9723298],
        [33953620, 61097867, 31631969, 22747749, 51115436, 63140833, 12228704, 6144370],
        [37728662, 10005775, 21120885, 21324423, 18950201, 60399078, 18197105, 30783535],
        [22654537, 20874696, 5298002, 18308346, 50094077, 28204034, 33439273, 24536311],
    ],
    [
        [12058958, 38157127, 1571331, 25947340, 37955233, 5792314, 22966821, 28623252],
        [31515253, 16425191, 19053638, 13203190, 38693053, 53107240, 23375652, 9509991],
        [45344702, 21288208, 18009913, 26461384, 55819508, 49157354, 23742099, 7291598],
        [9840135, 66438006, 18483451, 28421186, 20026337, 58077061, 422781, 8601273],
        [28148229, 2994918, 27587649, 15754209, 10760655, 11827684, 3447360, 13038269],
    ],
    [
        [23506627, 47866008, 16094468, 10483047, 2205871, 38010137, 9948533, 14213457],
        [51301454, 38200456, 32264654, 31721981, 38677024, 15369636, 13345242, 12888217],
        [41553852, 11262407, 15393762, 28053375, 27020988, 23638553, 15746731, 19053145],
        [36579026, 18270931, 27352641, 13026480, 14921350, 23783420, 17867630, 2416354],
        [14906452, 40435261, 1881776, 110286, 14762166, 51698274, 29485317, 26839020],
    ],
    [
        [36941495, 27766973, 28940424, 11394711, 27438489, 25562069, 26681507, 10998669],
        [36215372, 15942947, 13496963, 1578103, 5615704, 13762106, 21938925, 25748605],
        [44684411, 8485549, 14202121, 31408600, 56741630, 55837866, 9534283, 4347864],
        [41898573, 12401139, 16683623, 14274703, 13234232, 64890630, 10179797, 16575424],
        [27875905, 17508415, 2986296, 22198244, 59885130, 41497872, 30112215, 10027869],
    ],
    [
        [12137096, 10189003, 4606920, 17420321, 60893196, 28045861, 24509522, 9532797],
        [46027469, 42736667, 21770782, 3158833, 18274537, 20907264, 14435534, 28948499],
        [60036822, 31527560, 8435800, 31140968, 21029287, 63805097, 18587704, 7187288],
        [36496197, 49598109, 2167409, 27613013, 1437963, 52269714, 21962038, 33263074],
        [24553433, 44066364, 23890077, 18467334, 7711976, 22339684, 1503367, 14489714],
    ],
    [
        [25538780, 38909836, 11067896, 8172909, 57852615, 43289359, 1029971, 26578521],
        [44693009, 39110971, 4680955, 26406215, 47840003, 31738292, 22807095, 13437332],
        [52800371, 37226093, 14056033, 32892243, 59611779, 27955530, 22119881, 9822069],
        [10932398, 52780132, 26726591, 18874930, 3004420, 42469196, 15402895, 20627394],
        [13650072, 35296656, 32072846, 15700663, 65536671, 1172025, 16590792, 22430450],
    ],
    [
        [1625781, 20843703, 19039339, 31702723, 42358737, 66201711, 13459926, 13071695],
        [10735089, 43255767, 1163203, 29229500, 46539838, 37832734, 19417534, 645660],
        [10926912, 51745064, 9276420, 29649852, 11834440, 50281537, 16952606, 23646891],
        [40119465, 54911878, 15484518, 10943917, 21046420, 61210496, 33004940, 32728015],
        [56608065, 32697648, 23208231, 6805936, 39727410, 55945967, 28289083, 8873791],
    ],
    [
        [65959878, 4738112, 3926380, 10862043, 32371874, 61628282, 20294981, 16864730],
        [56561659, 18746768, 23963449, 31770816, 37433534, 30169392, 29424909, 15950602],
        [26146621, 49890171, 2059937, 26571140, 14785527, 40322263, 31000088, 8164080],
        [59722878, 43018220, 28090256, 8204365, 37606286, 33318247, 32585212, 20324338],
        [37170910, 11132844, 23104151, 4412547, 22673660, 16697926, 17890605, 27252765],
    ],
    [
        [8353780, 58789680, 6820533, 32456528, 25330401, 56539401, 9568371, 25746685],
        [2680348, 66687371, 17883740, 8554891, 15915195, 12849492, 16725649, 28996192],
        [28251720, 39635454, 1003764, 18909727, 18010728, 29787573, 8653274, 23072237],
        [10497532, 33015625, 3040924, 21735195, 22601672, 25864931, 3205301, 8323174],
        [59090533, 50894543, 7182325, 2923969, 11985571, 28672584, 16010222, 23659181],
    ],
    [
        [38616001, 41808039, 30805189, 19212317, 12876451, 415260, 16482156, 19135457],
        [40467780, 22988617, 7478296, 3493748, 39452728, 65090227, 9461946, 1004041],
        [20282351, 27331070, 5075150, 22321285, 30486221, 139236, 11267738, 28509890],
        [41996424, 5653186, 9497877, 19295112, 42023724, 32226583, 5210683, 23084723],
        [6176890, 9602697, 15415506, 14166852, 66157538, 34230251, 6378644, 19078039],
    ],
    [
        [55255955, 14982908, 9890276, 11446805, 7032176, 22656843, 3746723, 33116453],
        [34184369, 22469947, 26840956, 3132889, 62297121, 20044623, 28583516, 24159402],
        [57370907, 63191667, 21690430, 20696601, 39827366, 21187266, 12514618, 25652742],
        [9274478, 60144529, 26348527, 4133041, 24350224, 13022863, 32600804, 22650514],
        [65934793, 36557157, 979582, 26853578, 52839571, 58601389, 26286182, 2348290],
    ],
    [
        [48871244, 66327099, 31662477, 8039171, 66644219, 41202866, 4294592, 14551757],
        [15733595, 58471720, 14749750, 22379749, 54358695, 35397073, 20972981, 25008449],
        [29114737, 62009279, 30016317, 601443, 34638582, 24947758, 20421277, 13118226],
        [4108954, 19092996, 17070588, 4659423, 18632215, 11540859, 20456722, 20533822],
        [32216618, 6979936, 33057178, 10286745, 61281538, 16153418, 17761088, 25650839],
    ],
    [
        [47542905, 29833573, 29441550, 32594432, 66402751, 21074722, 3829665, 3702836],
        [22910516, 4441481, 26335360, 20549209, 55844053, 58348382, 22016502, 17993719],
        [19432070, 8213656, 228525, 22084330, 18805426, 32282601, 7584431, 29435530],
        [55834632, 33152893, 8643314, 20249381, 65961786, 57282333, 32569435, 32529637],
        [21236535, 17841544, 22875556, 9790544, 9397194, 7655609, 1556090, 10264607],
    ],
    [
        [57611263, 17103640, 25400732, 10351185, 27341767, 16699522, 5713078, 23113799],
        [22897310, 38729801, 27152753, 27894431, 24717523, 33363425, 24480517, 23282687],
        [11492034, 37493133, 5937307, 10306897, 59674459, 46241178, 26472371, 12932189],
        [32215109, 44198188, 1000049, 17399741, 24827135, 2900013, 32482825, 4866172],
        [16794044, 26874452, 25175866, 5060729, 2646223, 9839092, 20536919, 28491149],
    ],
    [
        [16653333, 34029816, 18779346, 1626930, 6447953, 47620431, 2386893, 10539672],
        [52532958, 43906412, 13513817, 9606713, 19546371, 26752031, 23970406, 32617894],
        [218729, 38861458, 20901055, 14889673, 12371736, 52484892, 29550879, 9320213],
        [1378552, 60113819, 18046499, 9804554, 40873024, 65594888, 25545301, 3302698],
        [36343043, 37207807, 15403588, 20848659, 32176941, 27976202, 31058460, 31602017],
    ],
    [
        [62471282, 22389951, 28826453, 33365379, 22961571, 65494854, 6343010, 22416189],
        [28966745, 10385893, 1919121, 31198595, 20713154, 14151803, 12290854, 25704404],
        [3214006, 29738138, 20094331, 7351483, 43171464, 26838859, 24503708, 23450728],
        [64842236, 51968528, 3142107, 4613764, 2189156, 24386697, 13409150, 30215442],
        [46723194, 9303527, 8405136, 14228396, 21010923, 31013902, 4691950, 8912065],
    ],
    [
        [49233641, 66024129, 1205659, 30871163, 13146134, 43612127, 106388, 3888141],
        [18945362, 30557051, 20639340, 8607758, 64209901, 56883699, 15940656, 27301716],
        [29217386, 64649972, 5350648, 26912959, 60058960, 905806, 20312853, 8936161],
        [11239605, 18647314, 1709544, 8615590, 23922051, 20646405, 26321411, 15822490],
        [25021212, 39199484, 3637194, 13047635, 31259849, 50014154, 11323602, 32723294],
    ],
    [
        [14733643, 59761629, 807533, 18565996, 43817217, 50300508, 26287550, 12969012],
        [59486327, 23595426, 8767690, 29417939, 39390219, 44052270, 9696763, 19754374],
        [39360769, 3484892, 2601013, 15019187, 37358287, 26086404, 10999263, 29725706],
        [30305771, 3820664, 426653, 14962311, 18330619, 5722784, 1972310, 28654076],
        [30760682, 12860254, 18445207, 24107070, 35944781, 34259765, 28612696, 5874292],
    ],
    [
        [54091413, 30836529, 22440147, 13389440, 4702119, 54254633, 24959533, 21455356],
        [59142556, 692655, 20465607, 23315269, 61994463, 12398087, 22152339, 17055620],
        [31702202, 61351087, 22222826, 5442645, 57446002, 3563169, 6991829, 12382382],
        [3368818, 39743496, 2589872, 17297877, 964701, 65407395, 25384744, 27756884],
        [27650912, 48743276, 32393888, 21398432, 26938189, 54768023, 4929679, 7108871],
    ],
    [
        [47582738, 42280477, 5260274, 12031069, 51587353, 24729137, 345357, 28759498],
        [11838794, 21425267, 27410213, 28219570, 23629151, 13643487, 23192532, 23583591],
        [4907527, 38569662, 5162401, 13558872, 56372022, 66214382, 10348559, 8579268],
        [22222447, 25423762, 106486, 31867922, 27118948, 51752619, 32277263, 15951395],
        [66277621, 35971056, 2363192, 27951424, 2255134, 26237214, 9307144, 986405],
    ],
    [
        [37591965, 56869768, 18827797, 8034596, 56798933, 38025012, 21073879, 23344331],
        [52828087, 24548832, 32801392, 16172038, 17768422, 44528197, 922321, 18743384],
        [10877844, 18662844, 10716088, 27275832, 31890254, 29135947, 21080826, 2241176],
        [22115494, 22326237, 17592315, 22101483, 40386349, 15074770, 8438620, 21798748],
        [47910816, 5299314, 1124791, 2656816, 63244638, 31437776, 25025427, 10290415],
    ],
    [
        [21878392, 31185774, 9126963, 23324589, 12288438, 45811879, 31274916, 7233956],
        [45447347, 51754034, 23857961, 24418218, 19931635, 19482257, 11595776, 23491520],
        [24621569, 2594534, 7249407, 32952156, 41407147, 37068652, 8106831, 20243877],
        [54892599, 43414588, 22243958, 14322964, 44802222, 22455138, 9464728, 28056046],
        [46296775, 15172545, 1956651, 17395776, 48956986, 16222572, 7515027, 10304304],
    ],
    [
        [16326777, 34067182, 11680152, 13090809, 33198910, 2630878, 26194520, 30307006],
        [16099073, 39765296, 13008289, 9749111, 11436566, 42252331, 5130763, 12077190],
        [3379872, 33210208, 28487573, 29810391, 15783239, 44078836, 335852, 31837512],
        [50559998, 43575158, 29147102, 20485764, 42578909, 35933688, 7354150, 21946422],
        [46188683, 65882928, 9666100, 4770338, 63610191, 38434873, 13594536, 3053980],
    ],
    [
        [4610590, 42659956, 3253516, 28236787, 30594275, 17715308, 22749905, 11372971],
        [36809548, 52988029, 8384127, 26069357, 13181012, 26729153, 23771947, 15209444],
        [58034912, 45023544, 13145336, 25104757, 52062118, 52665554, 512048, 18290279],
        [47816052, 6269405, 5810051, 28205761, 48042238, 31765615, 15344188, 12591228],
        [22209592, 19962530, 6669761, 22983845, 54405004, 36114303, 22083972, 11585738],
    ],
    [
        [10122284, 51261832, 18586848, 25817631, 37622312, 33651425, 11511273, 23666654],
        [16786924, 8079149, 20144945, 22485904, 23530723, 51644791, 6688474, 2753385],
        [55069397, 53864383, 10405220, 24942238, 1801549, 62538135, 18395305, 12000518],
        [59412485, 16769143, 4832711, 600137, 15042369, 52790722, 1665944, 1073953],
        [29226949, 47302383, 3375068, 95371, 35144248, 64982183, 18605945, 21703167],
    ],
    [
        [958738, 6142053, 22787506, 13403747, 27427176, 30173216, 9521868, 22566814],
        [45300552, 65699131, 190776, 21242303, 33689451, 2975080, 6937131, 24791188],
        [66211742, 65412605, 10516000, 24829017, 1029405, 53374679, 27141246, 21852748],
        [9979003, 17057936, 1240203, 8572464, 46032924, 40568684, 2272257, 31530999],
        [40680514, 1372286, 10536476, 6484876, 41761443, 57673361, 2548810, 289947],
    ],
    [
        [38224702, 21341595, 33333741, 3044198, 57193580, 47614136, 9436540, 28890316],
        [4536155, 65267604, 30320610, 7289780, 10322584, 26313058, 21156253, 17029576],
        [5750169, 46957207, 1496778, 16437412, 2769937, 12132989, 15579462, 31616555],
        [56193361, 64797597, 10782458, 11896649, 48575168, 24573846, 14812901, 12670966],
        [12899244, 51092069, 24904525, 5447716, 39640209, 60034210, 8373526, 22779967],
    ],
    [
        [62817163, 62528162, 15969745, 12027568, 46812944, 59600297, 27825401, 23306879],
        [50075179, 37237915, 19668977, 30504402, 66133750, 65955043, 23757577, 6259747],
        [54666314, 3364297, 3431581, 1934325, 12000699, 35355773, 10805694, 27901368],
        [22278394, 6434596, 7197479, 8351935, 36796669, 1756600, 8452294, 20202871],
        [27126100, 37737646, 24922539, 6322986, 12117782, 22725522, 12286646, 3171874],
    ],
    [
        [25877630, 14991203, 8417773, 4360939, 32274726, 53747299, 10826988, 17784323],
        [65609268, 53082020, 25933275, 14100839, 5617096, 12296358, 24469580, 10103496],
        [236941, 60091574, 14590795, 20597126, 41260406, 3919104, 26498826, 29458789],
        [19734135, 12997416, 7062794, 7557125, 59006644, 22854261, 12061930, 3856149],
        [4600720, 6318508, 28640364, 5400010, 38336606, 18147704, 2888662, 8915030],
    ],
    [
        [7780354, 41174160, 4671773, 3788734, 55790898, 12340678, 10822519, 12005479],
        [66035459, 47465115, 5229440, 15942271, 31039128, 15308595, 31601442, 32512854],
        [9309240, 62831198, 24120896, 25388372, 63061522, 59336377, 30619486, 30435571],
        [17940426, 35390477, 4300796, 20466893, 42423864, 30918551, 27045415, 17254947],
        [8343590, 40999216, 10106116, 26857446, 62368071, 45057162, 32892389, 2995444],
    ],
    [
        [1673112, 12183334, 27875497, 8251608, 45632790, 10852134, 21366119, 33108071],
        [37605354, 49496356, 29370857, 32310290, 59599232, 11044025, 11257465, 1965756],
        [64643482, 58266251, 33436142, 12379649, 48154835, 11738561, 11632452, 22512675],
        [58525902, 48886391, 3455869, 24776520, 49398327, 51391955, 32420054, 13952851],
        [7891137, 51871621, 4006126, 3894548, 31026685, 39320982, 18965134, 21724836],
    ],
    [
        [26640544, 40588217, 16835876, 27527330, 24562031, 41433911, 22560143, 31765999],
        [28131074, 36706600, 20359547, 26651051, 10782587, 51869949, 19204851, 1277336],
        [41237529, 12708175, 20670391, 22075739, 15657506, 49938192, 5933992, 1072598],
        [64428513, 40219911, 20105203, 3290258, 12730736, 47112760, 19989783, 17666927],
        [62580687, 34530814, 27884635, 28067849, 27317007, 24891250, 10045148, 21530131],
    ],
    [
        [63492585, 34251281, 8340245, 6676, 64079266, 40727728, 23961552, 1353353],
        [63879796, 27288330, 22265842, 28906375, 22078165, 45540663, 27906840, 21232712],
        [24053945, 55675563, 26866850, 17430981, 63052355, 44641021, 486840, 20479986],
        [12849638, 27056188, 31898965, 690354, 65810874, 40740167, 17861430, 21965926],
        [26368286, 53160743, 21655274, 10488127, 47025808, 56769717, 11295639, 6635057],
    ],
    [
        [62867877, 27281193, 6513593, 29987969, 20715649, 9407608, 2547304, 14386099],
        [6736572, 6776276, 22343488, 32935481, 6850808, 32360583, 32312663, 31689715],
        [42179715, 11077102, 15266781, 6814558, 34776093, 4639626, 24950286, 5012345],
        [13943914, 5749893, 19720938, 2800281, 53593449, 27000334, 31067300, 19982392],
        [10704438, 31186593, 20740620, 32290705, 42649447, 24811101, 24166493, 12192185],
    ],
    [
        [41691397, 16338041, 7089830, 33409219, 49788395, 28961508, 15896010, 23512801],
        [24563342, 34260095, 5585062, 31498990, 16485136, 18419707, 4928851, 31071589],
        [28931959, 1542450, 32270656, 1005808, 31306575, 56145503, 29921711, 27542440],
        [52172762, 45048870, 18525787, 21986947, 58827907, 55895498, 22205597, 19509588],
        [16679941, 62702409, 23277947, 12060408, 1085676, 44724393, 11823166, 16252638],
    ],
    [
        [14251580, 61876720, 25567287, 10781428, 34480484, 65318969, 22504489, 12623743],
        [46446827, 30188535, 17643797, 17192187, 8291894, 41953948, 29633174, 22334805],
        [61040715, 46276454, 14224241, 28818781, 52584155, 11407736, 24503067, 19228719],
        [48044738, 45920205, 23766749, 5725184, 36925087, 61295717, 14553197, 29788062],
        [9269836, 62804476, 7446509, 11143915, 15227044, 42687556, 32660008, 7934392],
    ],
    [
        [7494696, 59642309, 18582025, 5946036, 719288, 27358179, 23284068, 1196570],
        [34550551, 29481075, 9566868, 19521267, 26799119, 43219606, 17299714, 21322360],
        [36934671, 35494055, 32799951, 22869002, 16275646, 26828087, 11035999, 906859],
        [22982361, 8498161, 2286212, 21822883, 60001029, 8706607, 31671485, 11733154],
        [28887129, 28397771, 29839934, 28554990, 39032360, 7454622, 2293034, 25333421],
    ],
    [
        [61194732, 17619369, 17129369, 32419387, 42741117, 40792605, 24453006, 14526995],
        [17916590, 4202922, 14932699, 10926124, 38643342, 66256258, 31976869, 16450663],
        [2141424, 48860573, 17719035, 14314260, 57437558, 39565485, 22099955, 13622585],
        [11018987, 61333593, 27043947, 32868465, 12051889, 63290265, 17281448, 8122813],
        [63837981, 46941426, 30346410, 19858796, 41242065, 8215736, 21597517, 15643095],
    ],
    [
        [56143819, 2469968, 27401813, 25553170, 43798116, 12219792, 10179638, 726814],
        [30212032, 25167614, 18545696, 2407482, 31462761, 63831972, 26158390, 9855692],
        [30331409, 23843453, 29480936, 24797575, 6806210, 44647824, 6485425, 23580412],
        [64799733, 16544683, 3457427, 29913666, 55204625, 48965338, 30916498, 13918706],
        [20444877, 32237695, 11957065, 27805744, 17743259, 24613026, 3999914, 17854126],
    ],
    [
        [27111931, 4039795, 28139740, 9174900, 29883113, 63205737, 4224796, 8561523],
        [62165003, 16178570, 23625800, 4450920, 31185146, 8353124, 17486218, 27175783],
        [35677884, 51877043, 14496261, 6120570, 63338159, 50303862, 28108822, 11964561],
        [49304005, 891678, 29328044, 30157552, 17691975, 15885122, 16878482, 3938320],
        [61709984, 27465073, 32216792, 7739279, 65232591, 42303934, 28462423, 5807028],
    ],
    [
        [35676550, 31183904, 25081189, 26098756, 23505337, 43505795, 24080503, 8732300],
        [8494389, 22963769, 4524343, 30931697, 14758714, 7490203, 27970494, 26201721],
        [37535447, 14579617, 32981696, 17516826, 51657718, 18351695, 21965352, 16569703],
        [3069917, 32429501, 30604788, 10014884, 24055391, 4549468, 29905749, 21578344],
        [60893069, 4643498, 10399591, 2893589, 10669752, 35118118, 14394052, 9666212],
    ],
    [
        [8542056, 15520733, 6210929, 33402807, 52466592, 21030544, 29208779, 28928634],
        [49743296, 20624257, 19172748, 23263659, 44921715, 50169435, 11577297, 3873483],
        [3472754, 41886421, 5778683, 32092874, 53299410, 20812340, 11251359, 9027255],
        [36647944, 3284067, 26601284, 8218507, 62696736, 33455812, 4506159, 2708442],
        [27252898, 12699067, 22326486, 3241756, 65077981, 26345488, 10160771, 18754842],
    ],
    [
        [60140955, 45803995, 30416872, 12156204, 42707956, 6743199, 17423180, 1301567],
        [177016, 10315466, 18584052, 22555470, 52090894, 28216220, 1314409, 28517443],
        [62352979, 56795298, 28983154, 25031862, 43826337, 35936861, 16318774, 31437350],
        [13024609, 59574808, 24121194, 15368560, 13155168, 64375153, 17461697, 9324773],
        [28622156, 15293139, 9908484, 20554385, 10917379, 44426706, 3451030, 2119659],
    ],
    [
        [2116008, 40814232, 28657010, 18888082, 29424254, 58576525, 2489592, 10037984],
        [28630489, 46795240, 32820492, 209853, 13671791, 5695110, 29212778, 8089791],
        [55220745, 26252318, 20974757, 26478864, 11728214, 34036405, 20634205, 1325976],
        [57215061, 43771027, 10828761, 8317655, 52046478, 30819755, 33045857, 16395393],
        [13938883, 46395049, 8188465, 21182506, 25382933, 16973451, 6608179, 28293434],
    ],
    [
        [56098921, 1581349, 17794729, 32218560, 53667009, 5612211, 25973659, 29691663],
        [10662719, 23859199, 23756995, 10649208, 22497145, 7619068, 7960695, 20842014],
        [2525642, 31654050, 6693085, 19906243, 62340846, 65367640, 32651008, 978803],
        [20766903, 232509, 14700681, 1573198, 14895074, 43743685, 28672379, 33221053],
        [51655140, 10927552, 15484655, 17040085, 37127843, 34311742, 31900322, 11995582],
    ],
    [
        [40776565, 43268163, 6500169, 1271050, 18004578, 29644416, 11209588, 1412636],
        [38739729, 59230452, 13535019, 29752389, 5168716, 58338139, 20714034, 25859893],
        [28404461, 28561825, 22989181, 19342012, 22836628, 22939040, 10470764, 20363831],
        [54682339, 21246484, 23813916, 1608424, 45950783, 62785806, 29430044, 19477985],
        [21070530, 25784077, 5077152, 8441593, 16693944, 27927729, 27071102, 21605798],
    ],
    [
        [57742815, 55137910, 5226223, 21438249, 51702750, 31766000, 29193266, 33479106],
        [25465536, 23987956, 31293031, 16168826, 47912681, 15424223, 17874322, 25733746],
        [14170848, 41505515, 4590113, 14822658, 34914650, 63899904, 22180644, 28513826],
        [64275200, 1057442, 29489481, 19101807, 60310305, 27939274, 24403940, 7463395],
        [22402356, 59505658, 3776432, 24429605, 41432454, 49305719, 9368399, 25143987],
    ],
    [
        [38136498, 56048824, 4991773, 10742205, 18291433, 7921753, 22668812, 24058846],
        [48458072, 56352047, 27214975, 31804070, 7733147, 48625097, 11917737, 21699757],
        [14319043, 58025941, 26413512, 24461118, 11797506, 48218935, 26154458, 21639944],
        [33632708, 47849952, 10198515, 25210683, 47179192, 25097372, 11101604, 18739121],
        [64674091, 10822781, 9324803, 29505339, 32233022, 36708640, 14934189, 14397235],
    ],
    [
        [45148248, 58370512, 12973774, 21787534, 4075458, 18743006, 20490462, 9805431],
        [8621002, 8842247, 28329376, 31142899, 5389225, 37242023, 15892333, 17252049],
        [63577441, 46753122, 13491631, 1650477, 24110626, 6503959, 14338661, 26299044],
        [47327338, 38548494, 16658168, 15037822, 9654738, 65002230, 4481920, 24032482],
        [33051208, 61313867, 32635209, 20376698, 41771601, 34099040, 30626936, 16382778],
    ],
    [
        [47830328, 17361108, 8863286, 664653, 50574080, 56383069, 9472031, 13098493],
        [62348621, 55943949, 25436610, 18908482, 18960963, 10259905, 20602465, 20685278],
        [55367660, 38546285, 22278574, 20637263, 3666502, 43055815, 6574968, 12812679],
        [58729869, 30328035, 23875727, 6747348, 50533783, 46912975, 16274760, 12048297],
        [1015750, 64585658, 26728766, 4406024, 6731216, 20300757, 15514380, 2603427],
    ],
    [
        [32070903, 1559026, 14174269, 1324975, 27945608, 33129758, 25053096, 5821698],
        [33869556, 1869097, 7980821, 28776124, 33321965, 40209137, 27444855, 10597537],
        [56857414, 51138195, 19829289, 30628341, 43603109, 7587011, 664973, 266751],
        [55789795, 16982677, 10164223, 15421070, 49050337, 30287123, 8031553, 9944407],
        [11146692, 34427094, 32598110, 25408568, 55660722, 31695402, 10292604, 11098050],
    ],
    [
        [39989915, 45256160, 31578815, 2484212, 14117461, 56987084, 10259075, 7185334],
        [30438979, 47404348, 31975036, 710060, 16458232, 42175205, 22627698, 20934140],
        [1577576, 54474789, 24903056, 5201573, 60284603, 25813480, 1933113, 27141609],
        [47342948, 62345573, 9767164, 14686294, 17093020, 13239794, 21433077, 9108699],
        [33635257, 27746456, 6314212, 6685212, 9121609, 8887217, 6598413, 2568324],
    ],
    [
        [57222313, 61855775, 27810050, 10511287, 58841832, 8790713, 3835167, 23354080],
        [52561565, 12309625, 738833, 24953905, 15662243, 580288, 521459, 30219480],
        [16056462, 42602404, 29756857, 28338981, 49687730, 58964774, 20234976, 15981515],
        [31533921, 30420667, 9502322, 28634638, 38185140, 29345336, 24000262, 32010811],
        [793151, 22578075, 21541437, 8497246, 4275239, 64327456, 29884602, 10184176],
    ],
    [
        [2935694, 52456741, 6690521, 30233480, 49674737, 15334311, 32914997, 18326127],
        [55953323, 30351207, 15636018, 6742140, 43928276, 44463493, 17192254, 12631191],
        [13897957, 43867322, 15244673, 1713699, 9415660, 17087120, 11272001, 4737839],
        [59607143, 10292120, 12393416, 26203702, 14077443, 59890855, 23318735, 1839100],
        [56569426, 10097927, 25244712, 24320385, 63473551, 6859645, 14144652, 27546423],
    ],
    [
        [56542721, 50605081, 24504775, 554439, 43386184, 43285627, 19978557, 3836416],
        [32008165, 9306027, 32571344, 26567165, 18354718, 13055337, 1812485, 1875715],
        [992053, 16103665, 139321, 28960284, 46929812, 2729047, 6092052, 7701722],
        [36507642, 48894573, 2922010, 3015029, 33745453, 1687811, 9160315, 24654006],
        [34233194, 43337489, 22752464, 25341449, 34468317, 35601092, 29286738, 19835579],
    ],
    [
        [25135042, 1690145, 1306025, 31446295, 29103561, 47742133, 23982857, 17542899],
        [50566185, 52566647, 17146906, 32096092, 40727991, 37164861, 15608553, 15079845],
        [16531590, 53286296, 4228393, 12964699, 3171432, 61229173, 18415626, 2032715],
        [9534075, 21070046, 5803870, 2895304, 986135, 46411488, 18164127, 9304562],
        [53207318, 39083484, 10280557, 8790810, 43923609, 24244826, 19024281, 5549472],
    ],
    [
        [17760542, 43931344, 30544396, 30736532, 6768468, 29645838, 2999644, 1436479],
        [49403385, 8678722, 19620352, 12588828, 23210959, 19464974, 26488188, 17973262],
        [20735679, 61472738, 19278730, 19571148, 34570327, 37437628, 22475275, 19644089],
        [33748030, 48768548, 22765703, 31358047, 59708402, 48845612, 11241282, 11084903],
        [17857552, 34461330, 28022915, 20184566, 3809130, 24156499, 18718749, 10855869],
    ],
];

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::super::adx_mux::tests::Rng;
    use super::super::bignum_mul_p25519_alt::bignum_mul_p25519_alt;
    use super::super::bignum_neg_p25519::bignum_neg_p25519;
    use super::super::edwards25519_scalarmulbase_alt::edwards25519_scalarmulbase_alt;
    use super::*;

    /// Zero, one, the group order minus one, and 2^255 - 1.
    const EDGE_SCALARS: [[u64; 4]; 4] = [
        [0; 4],
        [1, 0, 0, 0],
        [
            0x5812631a5cf5d3ec,
            0x14def9dea2f79cd6,
            0,
            0x1000000000000000,
        ],
        [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1],
    ];

    fn mul(x: &[u64; 4], y: &[u64; 4]) -> [u64; 4] {
        let mut z = [0; 4];
        bignum_mul_p25519_alt(&mut z, x, y);
        z
    }

    /// `[scalar]B` in extended coordinates.
    fn base_mul(scalar: &[u64; 4]) -> [u64; 16] {
        let mut affine = [0; 8];
        edwards25519_scalarmulbase_alt(&mut affine, scalar);
        let (x, y) = (
            affine[..4].try_into().unwrap(),
            affine[4..].try_into().unwrap(),
        );
        let mut p = [0; 16];
        p[..8].copy_from_slice(&affine);
        p[8] = 1;
        p[12..].copy_from_slice(&mul(x, y));
        p
    }

    #[test]
    fn matches_generic() {
        let Some(token) = HaveAvx2::check() else {
            return;
        };

        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let check = |base: &[u64; 4], scalars: &[[u64; 4]; 2], points: &[[u64; 16]; 2]| {
            let (mut want, mut got) = ([0; 12], [0; 12]);
            crate::low::generic::edwards25519_msm::edwards25519_msm(
                &mut want, base, scalars, points,
            );
            edwards25519_msm(&mut got, base, scalars, points, token);
            // The same projective point: X1 Z2 = X2 Z1 and Y1 Z2 = Y2 Z1.
            let c =
                |p: &[u64; 12], i: usize| -> [u64; 4] { p[4 * i..4 * i + 4].try_into().unwrap() };
            for i in 0..2 {
                assert_eq!(
                    mul(&c(&want, i), &c(&got, 2)),
                    mul(&c(&got, i), &c(&want, 2)),
                    "{base:x?} {scalars:x?} {points:x?}"
                );
            }
        };

        let identity = [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0];
        for _ in 0..64 {
            let points = [base_mul(&rng.words(253)), base_mul(&rng.words(253))];
            for scalar in EDGE_SCALARS {
                check(&rng.words(253), &[scalar, rng.words(128)], &points);
                check(&scalar, &[rng.words(129), scalar], &points);
                check(&scalar, &[scalar, scalar], &[identity, points[1]]);
            }
            check(&rng.words(253), &[rng.words(255), rng.words(255)], &points);
        }
    }

    #[test]
    fn base_odd_multiples() {
        if HaveAvx2::check().is_none() {
            return;
        }

        for (scalar, want) in [
            ([1, 0, 0, 0], &BASE_ODD_MULTIPLES_LIMBS),
            ([0, 0, 1, 0], &BASE128_ODD_MULTIPLES_LIMBS),
        ] {
            let p = base_mul(&scalar);
            let c = |i: usize| -> [u64; 4] { p[4 * i..4 * i + 4].try_into().unwrap() };
            // SAFETY: the CPU has AVX2, checked above
            let table = unsafe { limb_table(&[c(0), c(1), c(2), c(3)]) };
            assert_eq!(&table, want);
        }
    }

    /// p, below its limbs' widths.
    const P: [u64; 4] = [
        0xffff_ffff_ffff_ffed,
        u64::MAX,
        u64::MAX,
        0x7fff_ffff_ffff_ffff,
    ];

    /// Which 32-bit lanes of each vector hold lane A's, B's, C's, and D's
    /// low limb; the high limb is two lanes on.
    const LOW_LANES: [usize; 4] = [0, 1, 4, 5];

    /// Each lane's ten limbs.
    fn limbs(x: &Fe4) -> [[u32; 10]; 4] {
        // SAFETY: both are 32 bytes, and every bit pattern is a valid [u32; 8]
        let vectors =
            x.0.map(|v| unsafe { core::mem::transmute::<__m256i, [u32; 8]>(v) });
        core::array::from_fn(|lane| {
            core::array::from_fn(|i| vectors[i / 2][LOW_LANES[lane] + 2 * (i % 2)])
        })
    }

    fn from_limbs(limbs: &[[u32; 10]; 4]) -> Fe4 {
        Fe4(core::array::from_fn(|j| {
            let mut lanes = [0; 8];
            for (lane, limbs) in limbs.iter().enumerate() {
                lanes[LOW_LANES[lane]] = limbs[2 * j];
                lanes[LOW_LANES[lane] + 2] = limbs[2 * j + 1];
            }
            v(lanes)
        }))
    }

    /// The field element of limbs of any size, reduced, by Horner's rule
    /// on the scalar field arithmetic.
    fn value(limbs: &[u32; 10]) -> [u64; 4] {
        let mut acc = [0u64; 4];
        for (i, &limb) in limbs.iter().enumerate().rev() {
            let mut t = [0; 4];
            bignum_mul_p25519_alt(&mut t, &acc, &[1 << (26 - (i & 1)), 0, 0, 0]);
            // Below p + 2^32, which fits.
            let mut carry = u64::from(limb);
            for t in &mut t {
                let (sum, c) = t.overflowing_add(carry);
                (*t, carry) = (sum, u64::from(c));
            }
            bignum_mul_p25519_alt(&mut acc, &t, &[1, 0, 0, 0]);
        }
        acc
    }

    /// Ten random limbs, each below `bounds`' limb plus one.
    fn random_limbs(rng: &mut Rng, bounds: &[u32; 10]) -> [u32; 10] {
        bounds.map(|b| (rng.next() % (u64::from(b) + 1)) as u32)
    }

    #[test]
    fn split_reduces() {
        if HaveAvx2::check().is_none() {
            return;
        }

        let mut rng = Rng(0x6a09_e667_f3bc_c908);
        let check = |x: &Fe4| {
            // SAFETY: the CPU has AVX2, checked above
            let got = unsafe { x.split() };
            for (got, limbs) in got.iter().zip(limbs(x)) {
                assert_eq!(*got, value(&limbs), "{limbs:x?}");
            }
        };

        // Around p, where the final subtraction decides: p - 1, p, and
        // 2^255 - 1, with each limb within its width.
        let mut p_1 = P;
        p_1[0] -= 1;
        // SAFETY: the CPU has AVX2, checked above
        check(&unsafe { Fe4::new(&[p_1, P, [u64::MAX, u64::MAX, u64::MAX, P[3]], [0; 4]]) });
        // Limbs of every size a lane holds, whose carries `split` folds.
        check(&from_limbs(&[[u32::MAX; 10]; 4]));
        for _ in 0..256 {
            check(&from_limbs(&core::array::from_fn(|_| {
                random_limbs(&mut rng, &[u32::MAX; 10])
            })));
        }
    }

    #[test]
    fn reduce_and_neg_keep_values() {
        if HaveAvx2::check().is_none() {
            return;
        }

        // 16p's limbs, the most `neg` subtracts from.
        // SAFETY: the CPU has AVX2, checked above
        let p_limbs = limbs(&unsafe { Fe4::new(&[P; 4]) })[0];
        let p16 = p_limbs.map(|l| l << 4);

        let mut rng = Rng(0xbb67_ae85_84ca_a73b);
        let check = |x: [[u32; 10]; 4]| {
            let fe = from_limbs(&x);
            // SAFETY: the CPU has AVX2, checked above
            let (reduced, negated) = unsafe { (fe.reduce(), fe.neg()) };
            for lane in 0..4 {
                let want = value(&x[lane]);
                assert_eq!(value(&limbs(&reduced)[lane]), want, "{x:x?}");
                let mut neg = [0; 4];
                bignum_neg_p25519(&mut neg, &want);
                assert_eq!(value(&limbs(&negated)[lane]), neg, "{x:x?}");
            }
        };

        check([[0; 10]; 4]);
        check([p16; 4]);
        for _ in 0..256 {
            check(core::array::from_fn(|_| random_limbs(&mut rng, &p16)));
        }
    }

    #[target_feature(enable = "avx,avx2")]
    fn limb_table(point: &[[u64; 4]; 4]) -> [[[u32; 8]; 5]; 64] {
        let p1 = Extended(Fe4::new(point));
        let p2 = p1.double();
        let mut table = [Cached::from(p1); 64];
        for i in 0..63 {
            table[i + 1] = Cached::from(p2.add(&table[i]));
        }
        table.map(|c| {
            c.0.0.map(|v| {
                let mut lanes = [0u32; 8];
                // SAFETY: `lanes` is 32 writable bytes
                unsafe { _mm256_storeu_si256(lanes.as_mut_ptr().cast(), v) };
                lanes
            })
        })
    }

    // A secret scalar's digits against a secret point, for `admin/ct-sde`.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_mul() {
        let mut rng = Rng(super::super::ct_sde::seed());
        let token = HaveAvx2::check().expect("AVX2");
        let point = base_mul(&rng.words(253));
        let digits: [i8; 64] = core::array::from_fn(|_| (rng.next() % 17) as i8 - 8);
        let mut res = [0; 16];
        super::super::ct_sde::traced(|| edwards25519_mul(&mut res, &digits, &point, token));
    }
}
