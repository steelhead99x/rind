// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Keccak-f1600 on eight states at once, one in each 64-bit element of
//! 25 AVX-512 vectors.

use core::arch::x86_64::*;

use super::cpu::HaveAvx512Vl;

/// Computes Keccak-f1600 on the first `n` of the eight states in `a`, from
/// one to eight. With AVX-512, two or more run all eight at once, which on
/// Zen 5 costs less than one four-way AVX2 permutation; one runs alone, and
/// without AVX-512 they run as `generic::keccak8` runs them. The states past
/// `n` are left unspecified.
#[inline]
pub(crate) fn sha3_keccak_nof8_f1600(a: &mut [[u64; 25]; 8], n: usize, rc: &[u64; 24]) {
    match HaveAvx512Vl::check() {
        Some(t) if n > 1 => permute(a, rc, t),
        _ => crate::low::generic::keccak8::sha3_keccak_nof8_f1600(a, n, rc),
    }
}

/// All eight states at once.
fn permute(a: &mut [[u64; 25]; 8], rc: &[u64; 24], _: HaveAvx512Vl) {
    // SAFETY: `HaveAvx512Vl` proves AVX-512 F.
    unsafe { permute_transposing(a, rc) }
}

/// Gathers each state's lanes into vectors, permutes them, and scatters them
/// back.
//
// Builds vectors element by element rather than loading through pointers,
// which Aeneas cannot translate, so `proofs/` can prove it; LLVM still loads
// each row whole.
#[target_feature(enable = "avx512f")]
fn permute_transposing(a: &mut [[u64; 25]; 8], rc: &[u64; 24]) {
    let b0 = transpose(rows(a, 0));
    let b1 = transpose(rows(a, 8));
    let b2 = transpose(rows(a, 16));
    let mut v = [
        b0[0],
        b0[1],
        b0[2],
        b0[3],
        b0[4],
        b0[5],
        b0[6],
        b0[7],
        b1[0],
        b1[1],
        b1[2],
        b1[3],
        b1[4],
        b1[5],
        b1[6],
        b1[7],
        b2[0],
        b2[1],
        b2[2],
        b2[3],
        b2[4],
        b2[5],
        b2[6],
        b2[7],
        _mm512_setr_epi64(
            a[0][24] as i64,
            a[1][24] as i64,
            a[2][24] as i64,
            a[3][24] as i64,
            a[4][24] as i64,
            a[5][24] as i64,
            a[6][24] as i64,
            a[7][24] as i64,
        ),
    ];

    keccak8_f1600(&mut v, rc);

    set_rows(
        a,
        0,
        transpose([v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]]),
    );
    set_rows(
        a,
        8,
        transpose([v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]]),
    );
    set_rows(
        a,
        16,
        transpose([v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23]]),
    );
    let lo = _mm512_extracti64x4_epi64::<0>(v[24]);
    let hi = _mm512_extracti64x4_epi64::<1>(v[24]);
    a[0][24] = _mm256_extract_epi64::<0>(lo) as u64;
    a[1][24] = _mm256_extract_epi64::<1>(lo) as u64;
    a[2][24] = _mm256_extract_epi64::<2>(lo) as u64;
    a[3][24] = _mm256_extract_epi64::<3>(lo) as u64;
    a[4][24] = _mm256_extract_epi64::<0>(hi) as u64;
    a[5][24] = _mm256_extract_epi64::<1>(hi) as u64;
    a[6][24] = _mm256_extract_epi64::<2>(hi) as u64;
    a[7][24] = _mm256_extract_epi64::<3>(hi) as u64;
}

/// Lanes `i` to `i + 7` of each state, a vector each.
#[inline]
#[target_feature(enable = "avx512f")]
fn rows(a: &[[u64; 25]; 8], i: usize) -> [__m512i; 8] {
    [
        row(&a[0], i),
        row(&a[1], i),
        row(&a[2], i),
        row(&a[3], i),
        row(&a[4], i),
        row(&a[5], i),
        row(&a[6], i),
        row(&a[7], i),
    ]
}

/// Lanes `i` to `i + 7` of `s`, lane `i` in element 0.
#[inline]
#[target_feature(enable = "avx512f")]
fn row(s: &[u64; 25], i: usize) -> __m512i {
    _mm512_setr_epi64(
        s[i] as i64,
        s[i + 1] as i64,
        s[i + 2] as i64,
        s[i + 3] as i64,
        s[i + 4] as i64,
        s[i + 5] as i64,
        s[i + 6] as i64,
        s[i + 7] as i64,
    )
}

/// Sets lanes `i` to `i + 7` of each state to a vector each.
#[inline]
#[target_feature(enable = "avx512f")]
fn set_rows(a: &mut [[u64; 25]; 8], i: usize, r: [__m512i; 8]) {
    set_row(&mut a[0], i, r[0]);
    set_row(&mut a[1], i, r[1]);
    set_row(&mut a[2], i, r[2]);
    set_row(&mut a[3], i, r[3]);
    set_row(&mut a[4], i, r[4]);
    set_row(&mut a[5], i, r[5]);
    set_row(&mut a[6], i, r[6]);
    set_row(&mut a[7], i, r[7]);
}

/// Sets lanes `i` to `i + 7` of `s` to `v`'s elements, element 0 in lane `i`.
//
// The one store through a pointer, which `proofs/` models by hand: LLVM splits
// a store built from `v`'s elements into 128-bit pieces.
#[inline]
#[target_feature(enable = "avx512f")]
fn set_row(s: &mut [u64; 25], i: usize, v: __m512i) {
    // SAFETY: the eight lanes are 64 bytes, exactly the width of one `__m512i`.
    unsafe { _mm512_storeu_si512(s[i..i + 8].as_mut_ptr().cast(), v) }
}

/// The 8x8 transpose of 64-bit elements: element `i` of vector `j` becomes
/// element `j` of vector `i`.
#[inline]
#[target_feature(enable = "avx512f")]
fn transpose(r: [__m512i; 8]) -> [__m512i; 8] {
    // Pairs of rows, interleaved: each 128-bit lane holds a 2x2 block.
    let t = [
        _mm512_unpacklo_epi64(r[0], r[1]),
        _mm512_unpackhi_epi64(r[0], r[1]),
        _mm512_unpacklo_epi64(r[2], r[3]),
        _mm512_unpackhi_epi64(r[2], r[3]),
        _mm512_unpacklo_epi64(r[4], r[5]),
        _mm512_unpackhi_epi64(r[4], r[5]),
        _mm512_unpacklo_epi64(r[6], r[7]),
        _mm512_unpackhi_epi64(r[6], r[7]),
    ];
    // Then a 4x4 transpose of those 128-bit blocks, in two steps.
    let s = [
        _mm512_shuffle_i64x2::<0x44>(t[0], t[2]),
        _mm512_shuffle_i64x2::<0xee>(t[0], t[2]),
        _mm512_shuffle_i64x2::<0x44>(t[4], t[6]),
        _mm512_shuffle_i64x2::<0xee>(t[4], t[6]),
        _mm512_shuffle_i64x2::<0x44>(t[1], t[3]),
        _mm512_shuffle_i64x2::<0xee>(t[1], t[3]),
        _mm512_shuffle_i64x2::<0x44>(t[5], t[7]),
        _mm512_shuffle_i64x2::<0xee>(t[5], t[7]),
    ];
    [
        _mm512_shuffle_i64x2::<0x88>(s[0], s[2]),
        _mm512_shuffle_i64x2::<0x88>(s[4], s[6]),
        _mm512_shuffle_i64x2::<0xdd>(s[0], s[2]),
        _mm512_shuffle_i64x2::<0xdd>(s[4], s[6]),
        _mm512_shuffle_i64x2::<0x88>(s[1], s[3]),
        _mm512_shuffle_i64x2::<0x88>(s[5], s[7]),
        _mm512_shuffle_i64x2::<0xdd>(s[1], s[3]),
        _mm512_shuffle_i64x2::<0xdd>(s[5], s[7]),
    ]
}

/// Keccak-f1600 on the eight states whose lane `i` is in the elements of
/// `state[i]`.
//
// A range loop, since Aeneas translates no iterator over `rc`.
#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "avx512f")]
pub(super) fn keccak8_f1600(state: &mut [__m512i; 25], rc: &[u64; 24]) {
    for i in 0..24 {
        *state = round(state, rc[i]);
    }
}

/// One round on the eight states whose lane `i` is in the elements of `a[i]`.
//
// Builds each array whole rather than in loops, which Aeneas cannot translate,
// so `proofs/` can prove it.
#[inline]
#[target_feature(enable = "avx512f")]
fn round(a: &[__m512i; 25], rc: u64) -> [__m512i; 25] {
    // Theta step.
    //
    // Compute the column parities C[x], then fold D[x] = C[x-1] ^ ROL(C[x+1], 1)
    // into every lane of column x.  This is fused with the rho and pi steps below.
    let c = [
        xor3(xor3(a[0], a[5], a[10]), a[15], a[20]),
        xor3(xor3(a[1], a[6], a[11]), a[16], a[21]),
        xor3(xor3(a[2], a[7], a[12]), a[17], a[22]),
        xor3(xor3(a[3], a[8], a[13]), a[18], a[23]),
        xor3(xor3(a[4], a[9], a[14]), a[19], a[24]),
    ];
    let c_rotated = [
        _mm512_rol_epi64::<1>(c[0]),
        _mm512_rol_epi64::<1>(c[1]),
        _mm512_rol_epi64::<1>(c[2]),
        _mm512_rol_epi64::<1>(c[3]),
        _mm512_rol_epi64::<1>(c[4]),
    ];

    // Rho and Pi steps.
    //
    // Rotate each lane by its rho offset and move it to its pi position
    // B[y, 2x + 3y] = ROL(A[x, y], RHO[x][y]), listed here in B's order.
    // `vprolq` takes its count as an immediate, so each lane is spelled out.
    macro_rules! rho_pi {
        ($(($x:literal, $y:literal, $rho:literal)),* $(,)?) => {[$(
            _mm512_rol_epi64::<$rho>(xor3(
                a[const { $x + 5 * $y }],
                c[const { ($x + 4) % 5 }],
                c_rotated[const { ($x + 1) % 5 }],
            )),
        )*]};
    }
    let b = rho_pi!(
        (0, 0, 0),
        (1, 1, 44),
        (2, 2, 43),
        (3, 3, 21),
        (4, 4, 14),
        (3, 0, 28),
        (4, 1, 20),
        (0, 2, 3),
        (1, 3, 45),
        (2, 4, 61),
        (1, 0, 1),
        (2, 1, 6),
        (3, 2, 25),
        (4, 3, 8),
        (0, 4, 18),
        (4, 0, 27),
        (0, 1, 36),
        (1, 2, 10),
        (2, 3, 15),
        (3, 4, 56),
        (2, 0, 62),
        (3, 1, 55),
        (4, 2, 39),
        (0, 3, 41),
        (1, 4, 2),
    );

    // Chi step.
    //
    // A[x, y] = B[x, y] ^ ((~B[x+1, y]) & B[x+2, y]).
    macro_rules! chi {
        ($($y:literal),*) => {[$(
            xor_andnot(b[const { 5 * $y }], b[const { 5 * $y + 1 }], b[const { 5 * $y + 2 }]),
            xor_andnot(b[const { 5 * $y + 1 }], b[const { 5 * $y + 2 }], b[const { 5 * $y + 3 }]),
            xor_andnot(b[const { 5 * $y + 2 }], b[const { 5 * $y + 3 }], b[const { 5 * $y + 4 }]),
            xor_andnot(b[const { 5 * $y + 3 }], b[const { 5 * $y + 4 }], b[const { 5 * $y }]),
            xor_andnot(b[const { 5 * $y + 4 }], b[const { 5 * $y }], b[const { 5 * $y + 1 }]),
        )*]};
    }
    let mut out = chi!(0, 1, 2, 3, 4);

    // Iota step.
    out[0] = _mm512_xor_si512(out[0], _mm512_set1_epi64(rc as i64));
    out
}

/// The round constants, for the callers that permute their own vectors.
pub(super) const RC: [u64; 24] = [
    0x00000000_00000001,
    0x00000000_00008082,
    0x80000000_0000808A,
    0x80000000_80008000,
    0x00000000_0000808B,
    0x00000000_80000001,
    0x80000000_80008081,
    0x80000000_00008009,
    0x00000000_0000008A,
    0x00000000_00000088,
    0x00000000_80008009,
    0x00000000_8000000A,
    0x00000000_8000808B,
    0x80000000_0000008B,
    0x80000000_00008089,
    0x80000000_00008003,
    0x80000000_00008002,
    0x80000000_00000080,
    0x00000000_0000800A,
    0x80000000_8000000A,
    0x80000000_80008081,
    0x80000000_00008080,
    0x00000000_80000001,
    0x80000000_80008008,
];

/// `a ^ b ^ c`
#[inline]
#[target_feature(enable = "avx512f")]
fn xor3(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
    _mm512_ternarylogic_epi64::<0x96>(a, b, c)
}

/// `a ^ (!b & c)`
#[inline]
#[target_feature(enable = "avx512f")]
fn xor_andnot(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
    _mm512_ternarylogic_epi64::<0xd2>(a, b, c)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Every count of states, each against the one-state routine, with
    // AVX-512 and, as `generic::keccak8` runs it, without.
    #[test]
    fn matches_one_at_a_time() {
        let states: [[u64; 25]; 8] = core::array::from_fn(|j| {
            core::array::from_fn(|i| ((j * 25 + i) as u64).wrapping_mul(0xbf58476d1ce4e5b9))
        });
        let mut want = states;
        for a in want.iter_mut() {
            super::super::sha3_keccak_f1600::sha3_keccak_f1600(a, &RC);
        }
        for n in 1..=8 {
            let mut got = states;
            sha3_keccak_nof8_f1600(&mut got, n, &RC);
            assert_eq!(got[..n], want[..n], "{n} states");
            let mut got = states;
            crate::low::generic::keccak8::sha3_keccak_nof8_f1600(&mut got, n, &RC);
            assert_eq!(got[..n], want[..n], "{n} states, four at a time");
        }
    }
}
