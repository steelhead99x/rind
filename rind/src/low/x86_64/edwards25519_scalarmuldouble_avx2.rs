// Copyright (c) 2016-2021 isis agora lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// SPDX-License-Identifier: BSD-3-Clause

//! Ed25519 verification's `[n]P + [m]B` on CPUs with AVX2 but without ADX,
//! ported from curve25519-dalek 5.0.0's AVX2 backend: its field arithmetic
//! (`backend/vector/avx2/field.rs`), its parallel point formulas
//! (`backend/vector/avx2/edwards.rs`), its width-5 and width-8 non-adjacent
//! forms, and its table of the base point's odd multiples. rind's code
//! converts in and out: s2n-bignum's verified routines compute the input
//! point's `T` and the affine result.
//!
//! The scalars and the point are public, so this runs in variable time.
//!
//! Each `Fe4` holds four field elements (lanes A, B, C, D) in radix
//! 2^25.5: ten limbs, alternately 26 and 25 bits, each limb pair's four
//! lanes interleaved in one vector as `(a0, b0, a1, b1, c0, d0, c1, d1)`.
//! Every operation's bound on its inputs' limbs is dalek's, which its
//! documentation gives with the formulas' derivation.

use core::arch::x86_64::*;

use super::bignum_inv_p25519::bignum_inv_p25519;
use super::bignum_mul_p25519_alt::bignum_mul_p25519_alt;
use super::cpu::HaveAvx2;

/// Computes `res := [scalar]point + [bscalar]B` as `edwards25519_scalarmuldouble`
/// does, for a point with reduced affine coordinates and scalars below 2^255.
pub(crate) fn edwards25519_scalarmuldouble(
    res: &mut [u64; 8],
    scalar: &[u64; 4],
    point: &[u64; 8],
    bscalar: &[u64; 4],
    _token: HaveAvx2,
) {
    assert!(scalar[3] >> 63 == 0 && bscalar[3] >> 63 == 0);
    assert!(point[3] >> 63 == 0 && point[7] >> 63 == 0);

    let x: &[u64; 4] = point[..4].try_into().unwrap();
    let y: &[u64; 4] = point[4..].try_into().unwrap();
    let mut t = [0u64; 4];
    bignum_mul_p25519_alt(&mut t, x, y);

    // SAFETY: `_token` proves the `avx` and `avx2` cpu features
    let [x, y, z] = unsafe { double_base(scalar, bscalar, &[*x, *y, [1, 0, 0, 0], t]) };

    let mut z_inv = [0u64; 4];
    bignum_inv_p25519(&mut z_inv, &z);
    let (res_x, res_y) = res.split_at_mut(4);
    bignum_mul_p25519_alt(res_x.try_into().unwrap(), &x, &z_inv);
    bignum_mul_p25519_alt(res_y.try_into().unwrap(), &y, &z_inv);
}

/// Computes `[a]A + [b]B` from `A`'s extended coordinates `(X, Y, Z, T)`,
/// returning the result's `(X, Y, Z)`, each reduced.
#[target_feature(enable = "avx,avx2")]
fn double_base(a: &[u64; 4], b: &[u64; 4], point: &[[u64; 4]; 4]) -> [[u64; 4]; 3] {
    // Its operands are public, but `admin/ct-vartime` holds every `vpmuludq`
    // to Intel's MXCSR mitigation alike. `target_feature` keeps this from
    // inlining into its caller, so the mitigation covers only the vector work.
    let _mcdt = crate::low::Mcdt::enter();
    let a_naf = non_adjacent_form(a, 5);
    let b_naf = non_adjacent_form(b, 8);

    // [A, 3A, 5A, ..., 15A]
    let a1 = Extended(Fe4::new(point));
    let a2 = a1.double();
    let mut table_a = [Cached::from(a1); 8];
    for i in 0..7 {
        table_a[i + 1] = Cached::from(a2.add(&table_a[i]));
    }

    let top = (0..256)
        .rev()
        .find(|&i| a_naf[i] != 0 || b_naf[i] != 0)
        .unwrap_or(0);

    let mut q = Extended(Fe4(EXTENDED_IDENTITY));
    for i in (0..=top).rev() {
        q = q.double();

        match a_naf[i] {
            0 => {}
            d if d > 0 => q = q.add(&table_a[d as usize / 2]),
            d => q = q.add(&table_a[d.unsigned_abs() as usize / 2].neg()),
        }

        match b_naf[i] {
            0 => {}
            d if d > 0 => q = q.add(&Cached(Fe4(BASE_ODD_MULTIPLES[d as usize / 2]))),
            d => q = q.add(&Cached(Fe4(BASE_ODD_MULTIPLES[d.unsigned_abs() as usize / 2])).neg()),
        }
    }

    let [x, y, z, _] = q.0.split();
    [x, y, z]
}

/// Returns the width-`w` non-adjacent form of `x < 2^255`: digits that are
/// zero or odd and below `2^(w-1)` in magnitude, with at most one nonzero
/// digit in any `w` consecutive.
fn non_adjacent_form(x: &[u64; 4], w: usize) -> [i8; 256] {
    let mut naf = [0i8; 256];
    let x = [x[0], x[1], x[2], x[3], 0];

    let width = 1 << w;
    let window_mask = width - 1;

    let mut pos = 0;
    let mut carry = 0;
    while pos < 256 {
        let (word, bit) = (pos / 64, pos % 64);
        let bit_buf = match bit < 64 - w {
            true => x[word] >> bit,
            false => (x[word] >> bit) | (x[word + 1] << (64 - bit)),
        };

        let window = carry + (bit_buf & window_mask);

        // An even window keeps the carry: with carry 1 its low bit was 1.
        if window & 1 == 0 {
            pos += 1;
            continue;
        }

        if window < width / 2 {
            carry = 0;
            naf[pos] = window as i8;
        } else {
            carry = 1;
            naf[pos] = (window as i8).wrapping_sub(width as i8);
        }

        pos += w;
    }

    naf
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
        let mut out = [[0u64; 5]; 4];
        for (i, l) in lanes.iter().enumerate() {
            let l = l.map(u64::from);
            out[0][i] = l[0] + (l[2] << 26);
            out[1][i] = l[1] + (l[3] << 26);
            out[2][i] = l[4] + (l[6] << 26);
            out[3][i] = l[5] + (l[7] << 26);
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
            l[0] += 19 * c[4];
            for i in 1..5 {
                l[i] += c[i - 1];
            }

            let mut q = (l[0] + 19) >> 51;
            for l in &l[1..] {
                q = (l + q) >> 51;
            }
            l[0] += 19 * q;
            for i in 0..4 {
                l[i + 1] += l[i] >> 51;
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

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::super::adx_mux::tests::Rng;
    use super::super::bignum_neg_p25519::bignum_neg_p25519;
    use super::super::edwards25519_scalarmulbase_alt::edwards25519_scalarmulbase_alt;
    use super::super::edwards25519_scalarmuldouble_alt::edwards25519_scalarmuldouble_alt;
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

    #[test]
    fn matches_alt() {
        let Some(token) = HaveAvx2::check() else {
            return;
        };

        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let check = |scalar: &[u64; 4], point: &[u64; 8], bscalar: &[u64; 4]| {
            let (mut want, mut got) = ([0; 8], [0; 8]);
            edwards25519_scalarmuldouble_alt(&mut want, scalar, point, bscalar);
            edwards25519_scalarmuldouble(&mut got, scalar, point, bscalar, token);
            assert_eq!(want, got, "{scalar:x?} {point:x?} {bscalar:x?}");
        };

        let identity = [0, 0, 0, 0, 1, 0, 0, 0];
        for _ in 0..64 {
            let mut point = [0; 8];
            edwards25519_scalarmulbase_alt(&mut point, &rng.words(253));

            for scalar in EDGE_SCALARS {
                check(&scalar, &point, &rng.words(255));
                check(&rng.words(255), &point, &scalar);
                check(&scalar, &identity, &scalar);
            }
            check(&rng.words(255), &point, &rng.words(255));
        }
    }

    #[test]
    fn base_odd_multiples() {
        if HaveAvx2::check().is_none() {
            return;
        }

        let mut b = [0; 8];
        edwards25519_scalarmulbase_alt(&mut b, &[1, 0, 0, 0]);
        let (x, y) = (b[..4].try_into().unwrap(), b[4..].try_into().unwrap());
        let mut t = [0; 4];
        bignum_mul_p25519_alt(&mut t, x, y);

        // SAFETY: the CPU has AVX2, checked above
        let table = unsafe { odd_multiples(&[*x, *y, [1, 0, 0, 0], t]) };
        for (got, want) in table.iter().zip(BASE_ODD_MULTIPLES_LIMBS) {
            assert_eq!(got, &want);
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
    fn odd_multiples(point: &[[u64; 4]; 4]) -> [[[u32; 8]; 5]; 64] {
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
}
