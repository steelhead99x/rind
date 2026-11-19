// Ported from XKCP's KeccakP-1600-times4-SIMD256.c, by the Keccak team
// (Guido Bertoni, Joan Daemen, Michaël Peeters, Gilles Van Assche, and Ronny
// Van Keer), under CC0-1.0.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Keccak-f1600 on four interleaved states with AVX2.
//!
//! A port of XKCP's `KeccakP1600times4_PermuteAll_24rounds`, the permutation
//! the SPHINCS+ team's AVX2 build runs: each of the 25 vectors holds one lane
//! of all four states, so the states stay in that layout between calls and
//! nothing transposes them. s2n-bignum's `sha3_keccak4_f1600`, which ML-KEM
//! and ML-DSA keep, transposes four separate states in and out on every
//! call. With AVX2 alone this measured the same as s2n-bignum's; compiled
//! again for AVX-512 VL, whose `vprolq` rotates in one instruction and whose
//! 32 registers hold the state, it took 0.6x its time for SLH-DSA signing.
//!
//! [`sha3_keccak4x_hash_blocks`] is the same permutation behind a first
//! block read straight from four buffers and its first 32 bytes written
//! straight to four more, by a 4x4 transpose in registers, as the C builds its
//! states. Storing the words of four states one at a time and loading them
//! back as vectors waits on every store.
//!
//! It runs xors, and-nots, shifts, rotates, and byte shuffles, none of which
//! take time that depends on their values. Its proof is planned in `ALGORITHMS.md`.

use core::arch::x86_64::*;

use super::cpu::{HaveAvx2, HaveAvx512Vl};

/// Keccak-f1600 on four states whose lane `i` of state `j` is `s[i][j]`.
pub(crate) fn sha3_keccak4x_f1600(_: HaveAvx2, s: &mut [[u64; 4]; 25], rc: &[u64; 24]) {
    match HaveAvx512Vl::check() {
        // SAFETY: the token proves AVX-512 F and VL, with AVX2.
        Some(_) => unsafe { permute_vl(s, rc) },
        // SAFETY: the token proves AVX2.
        None => unsafe { permute(s, rc) },
    }
}

/// Four states that each absorb one block, `blocks[j]` (the padded rate of
/// state `j`, the capacity zero), are permuted once, and the first 32 bytes of
/// each are returned.
pub(crate) fn sha3_keccak4x_hash_blocks(
    _: HaveAvx2,
    blocks: &[[u8; RATE]; 4],
    rc: &[u64; 24],
) -> [[u8; 32]; 4] {
    match HaveAvx512Vl::check() {
        // SAFETY: the token proves AVX-512 F and VL, with AVX2.
        Some(_) => unsafe { hash_blocks_vl(blocks, rc) },
        // SAFETY: the token proves AVX2.
        None => unsafe { hash_blocks(blocks, rc) },
    }
}

/// The 24 rounds on the 25 vectors in `$a`, in place: two a step, from `$a`
/// into `e` and back, all twelve written out as XKCP's C is. A macro, since a
/// function taking the vectors by reference keeps them in memory, and
/// `#[inline(always)]` is refused with `#[target_feature]`.
macro_rules! rounds {
    ($round:ident, $a:ident, $rc:ident) => {{
        let mut c = [_mm256_setzero_si256(); 5];
        for x in 0..5 {
            c[x] = x5($a[x], $a[x + 5], $a[x + 10], $a[x + 15], $a[x + 20]);
        }
        let mut e = [_mm256_setzero_si256(); 25];
        $round(&$a, &mut e, &mut c, $rc[0]);
        $round(&e, &mut $a, &mut c, $rc[1]);
        $round(&$a, &mut e, &mut c, $rc[2]);
        $round(&e, &mut $a, &mut c, $rc[3]);
        $round(&$a, &mut e, &mut c, $rc[4]);
        $round(&e, &mut $a, &mut c, $rc[5]);
        $round(&$a, &mut e, &mut c, $rc[6]);
        $round(&e, &mut $a, &mut c, $rc[7]);
        $round(&$a, &mut e, &mut c, $rc[8]);
        $round(&e, &mut $a, &mut c, $rc[9]);
        $round(&$a, &mut e, &mut c, $rc[10]);
        $round(&e, &mut $a, &mut c, $rc[11]);
        $round(&$a, &mut e, &mut c, $rc[12]);
        $round(&e, &mut $a, &mut c, $rc[13]);
        $round(&$a, &mut e, &mut c, $rc[14]);
        $round(&e, &mut $a, &mut c, $rc[15]);
        $round(&$a, &mut e, &mut c, $rc[16]);
        $round(&e, &mut $a, &mut c, $rc[17]);
        $round(&$a, &mut e, &mut c, $rc[18]);
        $round(&e, &mut $a, &mut c, $rc[19]);
        $round(&$a, &mut e, &mut c, $rc[20]);
        $round(&e, &mut $a, &mut c, $rc[21]);
        $round(&$a, &mut e, &mut c, $rc[22]);
        $round(&e, &mut $a, &mut c, $rc[23]);
    }};
}

/// Defines `$permute`, Keccak-f1600 on the 25 vectors, and the round it runs,
/// for the target features `$features`, rotating with `$rol`. Each gets its
/// own copy, compiled for its features, since a routine compiled for fewer
/// cannot inline the AVX-512 VL rotation.
macro_rules! keccak4x {
    ($permute:ident, $hash:ident, $round:ident, $rol:ident, $features:literal) => {
        /// Keccak-f1600 on four states whose lane `i` of state `j` is `s[i][j]`.
        #[target_feature(enable = $features)]
        fn $permute(s: &mut [[u64; 4]; 25], rc: &[u64; 24]) {
            let mut a = [_mm256_setzero_si256(); 25];
            for i in 0..25 {
                // SAFETY: `s[i]` is 32 bytes; the load needs no alignment.
                a[i] = unsafe { _mm256_loadu_si256(s[i].as_ptr().cast()) };
            }
            rounds!($round, a, rc);
            for i in 0..25 {
                // SAFETY: as the load, writing.
                unsafe { _mm256_storeu_si256(s[i].as_mut_ptr().cast(), a[i]) };
            }
        }

        /// Four states each absorbing one whole block, `blocks[j]`, the padded
        /// rate of state `j` over a zero capacity, permuted once, and the first
        /// 32 bytes of each squeezed. The vectors are made and unmade in
        /// registers by a 4x4 transpose, as XKCP's four-way SHAKE does: words
        /// stored one at a time and loaded back as a vector would wait on every
        /// store.
        #[target_feature(enable = $features)]
        fn $hash(blocks: &[[u8; RATE]; 4], rc: &[u64; 24]) -> [[u8; 32]; 4] {
            let mut a = [_mm256_setzero_si256(); 25];
            for g in 0..4 {
                // SAFETY: each block is 136 bytes and `32 * g + 32 <= 128`.
                let v = core::array::from_fn::<_, 4, _>(|j| unsafe {
                    _mm256_loadu_si256(blocks[j].as_ptr().add(32 * g).cast())
                });
                let t = transpose(v);
                a[4 * g..4 * g + 4].copy_from_slice(&t);
            }
            let last = |j: usize| i64::from_le_bytes(*blocks[j][128..].first_chunk().unwrap());
            a[16] = _mm256_set_epi64x(last(3), last(2), last(1), last(0));
            rounds!($round, a, rc);
            let t = transpose([a[0], a[1], a[2], a[3]]);
            let mut out = [[0u8; 32]; 4];
            for j in 0..4 {
                // SAFETY: `out[j]` is 32 bytes.
                unsafe { _mm256_storeu_si256(out[j].as_mut_ptr().cast(), t[j]) };
            }
            out
        }

/// One round from `a` into `e`, lane `x + 5y` at index `x + 5y`, given
        /// θ's column parities `c` of `a`, which it replaces with those of `e`.
        /// Written out one row of `e` at a time, as XKCP's
        /// `thetaRhoPiChiIotaPrepareTheta`, so few vectors are live at once: θ's
        /// mix `d`; then for each row, the five lanes π moves there, each rotated
        /// by ρ's offset from FIPS 202, and χ across them, with ι on the first.
        /// Closures and loops would hide the AVX2 target feature or the constant
        /// rotations from the compiler, so nothing here is either.
        #[target_feature(enable = $features)]
        #[inline]
        #[rustfmt::skip]
        fn $round(a: &[__m256i; 25], e: &mut [__m256i; 25], c: &mut [__m256i; 5], rc: u64) {
        let (rho8, rho56) = (rho8(), rho56());
        let d0 = _mm256_xor_si256(c[4], $rol::<1, 63>(c[1]));
        let d1 = _mm256_xor_si256(c[0], $rol::<1, 63>(c[2]));
        let d2 = _mm256_xor_si256(c[1], $rol::<1, 63>(c[3]));
        let d3 = _mm256_xor_si256(c[2], $rol::<1, 63>(c[4]));
        let d4 = _mm256_xor_si256(c[3], $rol::<1, 63>(c[0]));
        *c = [_mm256_setzero_si256(); 5];
        let b0 = _mm256_xor_si256(a[0], d0);
        let b1 = $rol::<44, 20>(_mm256_xor_si256(a[6], d1));
        let b2 = $rol::<43, 21>(_mm256_xor_si256(a[12], d2));
        let b3 = $rol::<21, 43>(_mm256_xor_si256(a[18], d3));
        let b4 = $rol::<14, 50>(_mm256_xor_si256(a[24], d4));
        e[0] = _mm256_xor_si256(b0, _mm256_andnot_si256(b1, b2));
        e[0] = _mm256_xor_si256(e[0], _mm256_set1_epi64x(rc as i64));
        c[0] = _mm256_xor_si256(c[0], e[0]);
        e[1] = _mm256_xor_si256(b1, _mm256_andnot_si256(b2, b3));
        c[1] = _mm256_xor_si256(c[1], e[1]);
        e[2] = _mm256_xor_si256(b2, _mm256_andnot_si256(b3, b4));
        c[2] = _mm256_xor_si256(c[2], e[2]);
        e[3] = _mm256_xor_si256(b3, _mm256_andnot_si256(b4, b0));
        c[3] = _mm256_xor_si256(c[3], e[3]);
        e[4] = _mm256_xor_si256(b4, _mm256_andnot_si256(b0, b1));
        c[4] = _mm256_xor_si256(c[4], e[4]);
        let b0 = $rol::<28, 36>(_mm256_xor_si256(a[3], d3));
        let b1 = $rol::<20, 44>(_mm256_xor_si256(a[9], d4));
        let b2 = $rol::<3, 61>(_mm256_xor_si256(a[10], d0));
        let b3 = $rol::<45, 19>(_mm256_xor_si256(a[16], d1));
        let b4 = $rol::<61, 3>(_mm256_xor_si256(a[22], d2));
        e[5] = _mm256_xor_si256(b0, _mm256_andnot_si256(b1, b2));
        c[0] = _mm256_xor_si256(c[0], e[5]);
        e[6] = _mm256_xor_si256(b1, _mm256_andnot_si256(b2, b3));
        c[1] = _mm256_xor_si256(c[1], e[6]);
        e[7] = _mm256_xor_si256(b2, _mm256_andnot_si256(b3, b4));
        c[2] = _mm256_xor_si256(c[2], e[7]);
        e[8] = _mm256_xor_si256(b3, _mm256_andnot_si256(b4, b0));
        c[3] = _mm256_xor_si256(c[3], e[8]);
        e[9] = _mm256_xor_si256(b4, _mm256_andnot_si256(b0, b1));
        c[4] = _mm256_xor_si256(c[4], e[9]);
        let b0 = $rol::<1, 63>(_mm256_xor_si256(a[1], d1));
        let b1 = $rol::<6, 58>(_mm256_xor_si256(a[7], d2));
        let b2 = $rol::<25, 39>(_mm256_xor_si256(a[13], d3));
        let b3 = _mm256_shuffle_epi8(_mm256_xor_si256(a[19], d4), rho8);
        let b4 = $rol::<18, 46>(_mm256_xor_si256(a[20], d0));
        e[10] = _mm256_xor_si256(b0, _mm256_andnot_si256(b1, b2));
        c[0] = _mm256_xor_si256(c[0], e[10]);
        e[11] = _mm256_xor_si256(b1, _mm256_andnot_si256(b2, b3));
        c[1] = _mm256_xor_si256(c[1], e[11]);
        e[12] = _mm256_xor_si256(b2, _mm256_andnot_si256(b3, b4));
        c[2] = _mm256_xor_si256(c[2], e[12]);
        e[13] = _mm256_xor_si256(b3, _mm256_andnot_si256(b4, b0));
        c[3] = _mm256_xor_si256(c[3], e[13]);
        e[14] = _mm256_xor_si256(b4, _mm256_andnot_si256(b0, b1));
        c[4] = _mm256_xor_si256(c[4], e[14]);
        let b0 = $rol::<27, 37>(_mm256_xor_si256(a[4], d4));
        let b1 = $rol::<36, 28>(_mm256_xor_si256(a[5], d0));
        let b2 = $rol::<10, 54>(_mm256_xor_si256(a[11], d1));
        let b3 = $rol::<15, 49>(_mm256_xor_si256(a[17], d2));
        let b4 = _mm256_shuffle_epi8(_mm256_xor_si256(a[23], d3), rho56);
        e[15] = _mm256_xor_si256(b0, _mm256_andnot_si256(b1, b2));
        c[0] = _mm256_xor_si256(c[0], e[15]);
        e[16] = _mm256_xor_si256(b1, _mm256_andnot_si256(b2, b3));
        c[1] = _mm256_xor_si256(c[1], e[16]);
        e[17] = _mm256_xor_si256(b2, _mm256_andnot_si256(b3, b4));
        c[2] = _mm256_xor_si256(c[2], e[17]);
        e[18] = _mm256_xor_si256(b3, _mm256_andnot_si256(b4, b0));
        c[3] = _mm256_xor_si256(c[3], e[18]);
        e[19] = _mm256_xor_si256(b4, _mm256_andnot_si256(b0, b1));
        c[4] = _mm256_xor_si256(c[4], e[19]);
        let b0 = $rol::<62, 2>(_mm256_xor_si256(a[2], d2));
        let b1 = $rol::<55, 9>(_mm256_xor_si256(a[8], d3));
        let b2 = $rol::<39, 25>(_mm256_xor_si256(a[14], d4));
        let b3 = $rol::<41, 23>(_mm256_xor_si256(a[15], d0));
        let b4 = $rol::<2, 62>(_mm256_xor_si256(a[21], d1));
        e[20] = _mm256_xor_si256(b0, _mm256_andnot_si256(b1, b2));
        c[0] = _mm256_xor_si256(c[0], e[20]);
        e[21] = _mm256_xor_si256(b1, _mm256_andnot_si256(b2, b3));
        c[1] = _mm256_xor_si256(c[1], e[21]);
        e[22] = _mm256_xor_si256(b2, _mm256_andnot_si256(b3, b4));
        c[2] = _mm256_xor_si256(c[2], e[22]);
        e[23] = _mm256_xor_si256(b3, _mm256_andnot_si256(b4, b0));
        c[3] = _mm256_xor_si256(c[3], e[23]);
        e[24] = _mm256_xor_si256(b4, _mm256_andnot_si256(b0, b1));
        c[4] = _mm256_xor_si256(c[4], e[24]);
        }
    };
}

keccak4x!(permute, hash_blocks, round, rol, "avx2");
keccak4x!(
    permute_vl,
    hash_blocks_vl,
    round_vl,
    rol_vl,
    "avx2,avx512f,avx512vl"
);

/// SHAKE256's rate in bytes.
const RATE: usize = 136;

/// The 4x4 transpose of 64-bit words: result `j` holds word `j` of each of
/// `v`, in order.
#[target_feature(enable = "avx2")]
#[inline]
fn transpose(v: [__m256i; 4]) -> [__m256i; 4] {
    let lo01 = _mm256_unpacklo_epi64(v[0], v[1]);
    let hi01 = _mm256_unpackhi_epi64(v[0], v[1]);
    let lo23 = _mm256_unpacklo_epi64(v[2], v[3]);
    let hi23 = _mm256_unpackhi_epi64(v[2], v[3]);
    [
        _mm256_permute2x128_si256::<0x20>(lo01, lo23),
        _mm256_permute2x128_si256::<0x20>(hi01, hi23),
        _mm256_permute2x128_si256::<0x31>(lo01, lo23),
        _mm256_permute2x128_si256::<0x31>(hi01, hi23),
    ]
}

/// The xor of five vectors.
#[target_feature(enable = "avx2")]
#[inline]
fn x5(a: __m256i, b: __m256i, c: __m256i, d: __m256i, e: __m256i) -> __m256i {
    _mm256_xor_si256(
        _mm256_xor_si256(_mm256_xor_si256(a, b), _mm256_xor_si256(c, d)),
        e,
    )
}

/// Each 64-bit lane of `v` rotated left by `L`, as shifts left by `L` and
/// right by `R`, its complement: Rust cannot compute `R` from `L` here.
#[target_feature(enable = "avx2")]
#[inline]
fn rol<const L: i32, const R: i32>(v: __m256i) -> __m256i {
    const { assert!(L + R == 64) };
    _mm256_or_si256(_mm256_slli_epi64::<L>(v), _mm256_srli_epi64::<R>(v))
}

/// `rol` as AVX-512 VL's one `vprolq`, where AVX2 takes three instructions.
#[target_feature(enable = "avx2,avx512f,avx512vl")]
#[inline]
fn rol_vl<const L: i32, const R: i32>(v: __m256i) -> __m256i {
    _mm256_rol_epi64::<L>(v)
}

/// The byte shuffle rotating each lane left by 8, which XKCP uses in place
/// of two shifts.
#[target_feature(enable = "avx2")]
#[inline]
fn rho8() -> __m256i {
    _mm256_set_epi64x(
        0x1E1D1C1B1A19181F,
        0x1615141312111017,
        0x0E0D0C0B0A09080F,
        0x0605040302010007,
    )
}

/// The byte shuffle rotating each lane left by 56.
#[target_feature(enable = "avx2")]
#[inline]
fn rho56() -> __m256i {
    _mm256_set_epi64x(
        0x181F1E1D1C1B1A19,
        0x1017161514131211,
        0x080F0E0D0C0B0A09,
        0x0007060504030201,
    )
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Each copy directly, since a CPU with AVX-512 VL runs only its own.
    // The block entry against four separate one-block SHAKE256 absorbs, for
    // each copy directly.
    #[test]
    fn hash_blocks_matches_one_state_at_a_time() {
        if HaveAvx2::check().is_none() {
            return;
        }
        let vl = HaveAvx512Vl::check().is_some();
        for seed in 0..32u64 {
            let blocks: [[u8; RATE]; 4] = core::array::from_fn(|j| {
                core::array::from_fn(|i| {
                    ((seed * 131 + (j * RATE + i) as u64).wrapping_mul(0x9e3779b97f4a7c15) >> 40)
                        as u8
                })
            });
            let want: [[u8; 32]; 4] = core::array::from_fn(|j| {
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
            // SAFETY: AVX2 was checked above.
            let mut got = vec![("avx2", unsafe {
                hash_blocks(&blocks, &crate::mid::sha3::RC)
            })];
            if vl {
                // SAFETY: AVX-512 F and VL were checked above.
                got.push(("avx512vl", unsafe {
                    hash_blocks_vl(&blocks, &crate::mid::sha3::RC)
                }));
            }
            for (name, got) in got {
                assert_eq!(got, want, "{name} seed {seed}");
            }
        }
    }

    #[test]
    fn matches_one_state_at_a_time() {
        if HaveAvx2::check().is_none() {
            return;
        }
        let vl = HaveAvx512Vl::check().is_some();
        for seed in 0..64u64 {
            let separate: [[u64; 25]; 4] = core::array::from_fn(|j| {
                core::array::from_fn(|i| {
                    (seed * 100 + (j * 25 + i) as u64).wrapping_mul(0xbf58476d1ce4e5b9)
                })
            });
            let mut want = separate;
            for state in want.iter_mut() {
                super::super::sha3_keccak_f1600::sha3_keccak_f1600(state, &crate::mid::sha3::RC);
            }
            let interleaved: [[u64; 4]; 25] =
                core::array::from_fn(|i| core::array::from_fn(|j| separate[j][i]));
            let mut avx2 = interleaved;
            // SAFETY: AVX2 was checked above.
            unsafe { permute(&mut avx2, &crate::mid::sha3::RC) };
            let mut got = vec![("avx2", avx2)];
            if vl {
                let mut with_vl = interleaved;
                // SAFETY: AVX-512 F and VL were checked above.
                unsafe { permute_vl(&mut with_vl, &crate::mid::sha3::RC) };
                got.push(("avx512vl", with_vl));
            }
            for (name, got) in got {
                for i in 0..25 {
                    for j in 0..4 {
                        assert_eq!(
                            got[i][j], want[j][i],
                            "{name} seed {seed} lane {i} state {j}"
                        );
                    }
                }
            }
        }
    }

    // What valgrind hides: the AVX-512 VL copies run on secret-seeded states
    // and blocks (`shake256_x4` hashes SK.seed), so `admin/ct-sde` compares
    // their traces for two seeds. The AVX2 copies run under ctgrind.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_keccak4x_vl() {
        use super::super::ct_sde;
        assert!(HaveAvx512Vl::check().is_some(), "AVX-512 VL");
        let mut x = ct_sde::seed();
        let mut next = move || {
            x = x.wrapping_add(0x9e3779b97f4a7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
            z ^ (z >> 31)
        };
        let mut s = [[0u64; 4]; 25];
        for lane in s.iter_mut().flatten() {
            *lane = next();
        }
        let mut blocks = [[0u8; RATE]; 4];
        for byte in blocks.iter_mut().flatten() {
            *byte = next() as u8;
        }
        // SAFETY: AVX-512 F and VL were checked above.
        ct_sde::traced(|| unsafe { permute_vl(&mut s, &crate::mid::sha3::RC) });
        // SAFETY: as above.
        ct_sde::traced(|| unsafe { hash_blocks_vl(&blocks, &crate::mid::sha3::RC) });
    }
}
