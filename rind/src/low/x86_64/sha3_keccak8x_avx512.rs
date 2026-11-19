// Keccak-f1600 as in XKCP's KeccakP-1600-times4-SIMD256.c, by the Keccak team
// (Guido Bertoni, Joan Daemen, Michaël Peeters, Gilles Van Assche, and Ronny
// Van Keer), under CC0-1.0, widened to eight states on 512-bit vectors.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! One SHAKE256 block of eight interleaved states with AVX-512.
//!
//! [`sha3_keccak4x_avx2`](super::sha3_keccak4x_avx2)'s round on `zmm`
//! vectors, each holding one lane of eight states, so eight SLH-DSA hashes
//! take the 24 rounds the four-way routine spends on four. AVX-512 rotates
//! in one `vprolq`, so the byte shuffles for the 8 and 56 bit rotations are
//! rotates here too. Zen 4 runs a 512-bit operation as two 256-bit halves,
//! yet the eight-way permutation still measures 1.3x the four-way's rate per
//! state there, since it also saves the four-way's loop and load overhead.
//!
//! It runs xors, and-nots, rotates, and shuffles, none of which take time
//! that depends on their values. Its proof is planned in `ALGORITHMS.md`.

use core::arch::x86_64::*;

use super::cpu::HaveAvx512Vl;

/// SHAKE256's rate in bytes.
const RATE: usize = 136;

/// Eight states that each absorb one block, `blocks[j]` (the padded rate of
/// state `j`, the capacity zero), are permuted once, and the first 32 bytes
/// of each are returned.
pub(crate) fn sha3_keccak8x_hash_blocks(
    _: HaveAvx512Vl,
    blocks: &[[u8; RATE]; 8],
    rc: &[u64; 24],
) -> [[u8; 32]; 8] {
    // SAFETY: the token proves AVX-512 F, which this function requires.
    unsafe { hash_blocks(blocks, rc) }
}

/// The 24 rounds on the 25 vectors in `a`, in place: two a step, from `a`
/// into `e` and back, written out as the four-way routine's are.
#[target_feature(enable = "avx512f")]
fn permute(a: &mut [__m512i; 25], rc: &[u64; 24]) {
    let mut c = [_mm512_setzero_si512(); 5];
    for x in 0..5 {
        c[x] = x5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]);
    }
    let mut e = [_mm512_setzero_si512(); 25];
    for r in (0..24).step_by(2) {
        round(a, &mut e, &mut c, rc[r]);
        round(&e, a, &mut c, rc[r + 1]);
    }
}

#[target_feature(enable = "avx512f")]
fn hash_blocks(blocks: &[[u8; RATE]; 8], rc: &[u64; 24]) -> [[u8; 32]; 8] {
    let mut a = [_mm512_setzero_si512(); 25];
    for g in 0..2 {
        // SAFETY: each block is 136 bytes and `64 * g + 64 <= 128`.
        let v = core::array::from_fn::<_, 8, _>(|j| unsafe {
            _mm512_loadu_si512(blocks[j].as_ptr().add(64 * g).cast())
        });
        a[8 * g..8 * g + 8].copy_from_slice(&transpose(v));
    }
    let last = |j: usize| i64::from_le_bytes(*blocks[j][128..].first_chunk().unwrap());
    a[16] = _mm512_set_epi64(
        last(7),
        last(6),
        last(5),
        last(4),
        last(3),
        last(2),
        last(1),
        last(0),
    );
    permute(&mut a, rc);
    let zero = _mm512_setzero_si512();
    let t = transpose([a[0], a[1], a[2], a[3], zero, zero, zero, zero]);
    let mut out = [[0u8; 32]; 8];
    for j in 0..8 {
        // SAFETY: `out[j]` is 32 bytes.
        unsafe { _mm256_storeu_si256(out[j].as_mut_ptr().cast(), _mm512_castsi512_si256(t[j])) };
    }
    out
}

/// The 8x8 transpose of 64-bit words: result `j` holds word `j` of each of
/// `v`, in order.
#[target_feature(enable = "avx512f")]
#[inline]
fn transpose(v: [__m512i; 8]) -> [__m512i; 8] {
    let lo = |i: usize| _mm512_unpacklo_epi64(v[i], v[i + 1]);
    let hi = |i: usize| _mm512_unpackhi_epi64(v[i], v[i + 1]);
    // `vshufi64x2` takes two of `x`'s four 128-bit parts, then two of `y`'s.
    let (l01, l23, l45, l67) = (lo(0), lo(2), lo(4), lo(6));
    let (h01, h23, h45, h67) = (hi(0), hi(2), hi(4), hi(6));
    // Rows `j` and `j + 1`, words `i` and `i + 4`, regrouped by pairs of rows.
    let p0 = _mm512_shuffle_i64x2::<0x88>(l01, l23);
    let p4 = _mm512_shuffle_i64x2::<0xDD>(l01, l23);
    let q0 = _mm512_shuffle_i64x2::<0x88>(l45, l67);
    let q4 = _mm512_shuffle_i64x2::<0xDD>(l45, l67);
    let p1 = _mm512_shuffle_i64x2::<0x88>(h01, h23);
    let p5 = _mm512_shuffle_i64x2::<0xDD>(h01, h23);
    let q1 = _mm512_shuffle_i64x2::<0x88>(h45, h67);
    let q5 = _mm512_shuffle_i64x2::<0xDD>(h45, h67);
    [
        _mm512_shuffle_i64x2::<0x88>(p0, q0),
        _mm512_shuffle_i64x2::<0x88>(p1, q1),
        _mm512_shuffle_i64x2::<0x88>(p4, q4),
        _mm512_shuffle_i64x2::<0x88>(p5, q5),
        _mm512_shuffle_i64x2::<0xDD>(p0, q0),
        _mm512_shuffle_i64x2::<0xDD>(p1, q1),
        _mm512_shuffle_i64x2::<0xDD>(p4, q4),
        _mm512_shuffle_i64x2::<0xDD>(p5, q5),
    ]
}

/// The xor of five vectors.
#[target_feature(enable = "avx512f")]
#[inline]
fn x5(a: __m512i, b: __m512i, c: __m512i, d: __m512i, e: __m512i) -> __m512i {
    _mm512_xor_si512(
        _mm512_xor_si512(_mm512_xor_si512(a, b), _mm512_xor_si512(c, d)),
        e,
    )
}

/// Each 64-bit lane of `v` rotated left by `L`, as one `vprolq`; `R`, the
/// complement the four-way routine's shifts take, keeps the two call
/// shapes alike.
#[target_feature(enable = "avx512f")]
#[inline]
fn rol<const L: i32, const R: i32>(v: __m512i) -> __m512i {
    const { assert!(L + R == 64) };
    _mm512_rol_epi64::<L>(v)
}

/// One round from `a` into `e`, lane `x + 5y` at index `x + 5y`, given
/// θ's column parities `c` of `a`, which it replaces with those of `e`, as
/// the four-way routine's round is.
#[target_feature(enable = "avx512f")]
#[inline]
#[rustfmt::skip]
fn round(a: &[__m512i; 25], e: &mut [__m512i; 25], c: &mut [__m512i; 5], rc: u64) {
    let d0 = _mm512_xor_si512(c[4], rol::<1, 63>(c[1]));
    let d1 = _mm512_xor_si512(c[0], rol::<1, 63>(c[2]));
    let d2 = _mm512_xor_si512(c[1], rol::<1, 63>(c[3]));
    let d3 = _mm512_xor_si512(c[2], rol::<1, 63>(c[4]));
    let d4 = _mm512_xor_si512(c[3], rol::<1, 63>(c[0]));
    *c = [_mm512_setzero_si512(); 5];
    let b0 = _mm512_xor_si512(a[0], d0);
    let b1 = rol::<44, 20>(_mm512_xor_si512(a[6], d1));
    let b2 = rol::<43, 21>(_mm512_xor_si512(a[12], d2));
    let b3 = rol::<21, 43>(_mm512_xor_si512(a[18], d3));
    let b4 = rol::<14, 50>(_mm512_xor_si512(a[24], d4));
    e[0] = _mm512_xor_si512(b0, _mm512_andnot_si512(b1, b2));
    e[0] = _mm512_xor_si512(e[0], _mm512_set1_epi64(rc as i64));
    c[0] = _mm512_xor_si512(c[0], e[0]);
    e[1] = _mm512_xor_si512(b1, _mm512_andnot_si512(b2, b3));
    c[1] = _mm512_xor_si512(c[1], e[1]);
    e[2] = _mm512_xor_si512(b2, _mm512_andnot_si512(b3, b4));
    c[2] = _mm512_xor_si512(c[2], e[2]);
    e[3] = _mm512_xor_si512(b3, _mm512_andnot_si512(b4, b0));
    c[3] = _mm512_xor_si512(c[3], e[3]);
    e[4] = _mm512_xor_si512(b4, _mm512_andnot_si512(b0, b1));
    c[4] = _mm512_xor_si512(c[4], e[4]);
    let b0 = rol::<28, 36>(_mm512_xor_si512(a[3], d3));
    let b1 = rol::<20, 44>(_mm512_xor_si512(a[9], d4));
    let b2 = rol::<3, 61>(_mm512_xor_si512(a[10], d0));
    let b3 = rol::<45, 19>(_mm512_xor_si512(a[16], d1));
    let b4 = rol::<61, 3>(_mm512_xor_si512(a[22], d2));
    e[5] = _mm512_xor_si512(b0, _mm512_andnot_si512(b1, b2));
    c[0] = _mm512_xor_si512(c[0], e[5]);
    e[6] = _mm512_xor_si512(b1, _mm512_andnot_si512(b2, b3));
    c[1] = _mm512_xor_si512(c[1], e[6]);
    e[7] = _mm512_xor_si512(b2, _mm512_andnot_si512(b3, b4));
    c[2] = _mm512_xor_si512(c[2], e[7]);
    e[8] = _mm512_xor_si512(b3, _mm512_andnot_si512(b4, b0));
    c[3] = _mm512_xor_si512(c[3], e[8]);
    e[9] = _mm512_xor_si512(b4, _mm512_andnot_si512(b0, b1));
    c[4] = _mm512_xor_si512(c[4], e[9]);
    let b0 = rol::<1, 63>(_mm512_xor_si512(a[1], d1));
    let b1 = rol::<6, 58>(_mm512_xor_si512(a[7], d2));
    let b2 = rol::<25, 39>(_mm512_xor_si512(a[13], d3));
    let b3 = _mm512_rol_epi64::<8>(_mm512_xor_si512(a[19], d4));
    let b4 = rol::<18, 46>(_mm512_xor_si512(a[20], d0));
    e[10] = _mm512_xor_si512(b0, _mm512_andnot_si512(b1, b2));
    c[0] = _mm512_xor_si512(c[0], e[10]);
    e[11] = _mm512_xor_si512(b1, _mm512_andnot_si512(b2, b3));
    c[1] = _mm512_xor_si512(c[1], e[11]);
    e[12] = _mm512_xor_si512(b2, _mm512_andnot_si512(b3, b4));
    c[2] = _mm512_xor_si512(c[2], e[12]);
    e[13] = _mm512_xor_si512(b3, _mm512_andnot_si512(b4, b0));
    c[3] = _mm512_xor_si512(c[3], e[13]);
    e[14] = _mm512_xor_si512(b4, _mm512_andnot_si512(b0, b1));
    c[4] = _mm512_xor_si512(c[4], e[14]);
    let b0 = rol::<27, 37>(_mm512_xor_si512(a[4], d4));
    let b1 = rol::<36, 28>(_mm512_xor_si512(a[5], d0));
    let b2 = rol::<10, 54>(_mm512_xor_si512(a[11], d1));
    let b3 = rol::<15, 49>(_mm512_xor_si512(a[17], d2));
    let b4 = _mm512_rol_epi64::<56>(_mm512_xor_si512(a[23], d3));
    e[15] = _mm512_xor_si512(b0, _mm512_andnot_si512(b1, b2));
    c[0] = _mm512_xor_si512(c[0], e[15]);
    e[16] = _mm512_xor_si512(b1, _mm512_andnot_si512(b2, b3));
    c[1] = _mm512_xor_si512(c[1], e[16]);
    e[17] = _mm512_xor_si512(b2, _mm512_andnot_si512(b3, b4));
    c[2] = _mm512_xor_si512(c[2], e[17]);
    e[18] = _mm512_xor_si512(b3, _mm512_andnot_si512(b4, b0));
    c[3] = _mm512_xor_si512(c[3], e[18]);
    e[19] = _mm512_xor_si512(b4, _mm512_andnot_si512(b0, b1));
    c[4] = _mm512_xor_si512(c[4], e[19]);
    let b0 = rol::<62, 2>(_mm512_xor_si512(a[2], d2));
    let b1 = rol::<55, 9>(_mm512_xor_si512(a[8], d3));
    let b2 = rol::<39, 25>(_mm512_xor_si512(a[14], d4));
    let b3 = rol::<41, 23>(_mm512_xor_si512(a[15], d0));
    let b4 = rol::<2, 62>(_mm512_xor_si512(a[21], d1));
    e[20] = _mm512_xor_si512(b0, _mm512_andnot_si512(b1, b2));
    c[0] = _mm512_xor_si512(c[0], e[20]);
    e[21] = _mm512_xor_si512(b1, _mm512_andnot_si512(b2, b3));
    c[1] = _mm512_xor_si512(c[1], e[21]);
    e[22] = _mm512_xor_si512(b2, _mm512_andnot_si512(b3, b4));
    c[2] = _mm512_xor_si512(c[2], e[22]);
    e[23] = _mm512_xor_si512(b3, _mm512_andnot_si512(b4, b0));
    c[3] = _mm512_xor_si512(c[3], e[23]);
    e[24] = _mm512_xor_si512(b4, _mm512_andnot_si512(b0, b1));
    c[4] = _mm512_xor_si512(c[4], e[24]);
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Eight blocks against eight one-state permutations, with the sizes of
    // the blocks' last words varied by seed.
    #[test]
    fn hash_blocks_matches_one_state_at_a_time() {
        let Some(vl) = HaveAvx512Vl::check() else {
            return;
        };
        for seed in 0..32u64 {
            let blocks: [[u8; RATE]; 8] = core::array::from_fn(|j| {
                core::array::from_fn(|i| {
                    ((seed * 131 + (j * RATE + i) as u64).wrapping_mul(0x9e3779b97f4a7c15) >> 40)
                        as u8
                })
            });
            let want: [[u8; 32]; 8] = core::array::from_fn(|j| {
                let mut state = [0u64; 25];
                for (word, bytes) in state.iter_mut().zip(blocks[j].as_chunks::<8>().0) {
                    *word = u64::from_le_bytes(*bytes);
                }
                super::super::sha3_keccak_f1600::sha3_keccak_f1600(
                    &mut state,
                    &crate::mid::sha3::RC,
                );
                core::array::from_fn(|i| state[i / 8].to_le_bytes()[i % 8])
            });
            let got = sha3_keccak8x_hash_blocks(vl, &blocks, &crate::mid::sha3::RC);
            assert_eq!(got, want, "seed {seed}");
        }
    }

    // The eight-way block hash, which valgrind cannot run, over secret blocks,
    // for `admin/ct-sde`.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_keccak8x() {
        let vl = HaveAvx512Vl::check().expect("AVX-512 VL");
        let mut x = super::super::ct_sde::seed();
        let blocks: [[u8; RATE]; 8] = core::array::from_fn(|_| {
            core::array::from_fn(|_| {
                x = x.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(1);
                (x >> 56) as u8
            })
        });
        super::super::ct_sde::traced(|| {
            sha3_keccak8x_hash_blocks(vl, &blocks, &crate::mid::sha3::RC)
        });
    }
}
