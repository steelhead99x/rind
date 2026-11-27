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
#[target_feature(enable = "avx512f")]
unsafe fn permute_transposing(a: &mut [[u64; 25]; 8], rc: &[u64; 24]) {
    let mut v = [_mm512_setzero_si512(); 25];
    for block in 0..3 {
        // SAFETY: each state has 25 lanes, so lanes `8 * block` on are in
        // bounds for the eight a 64-byte load reads.
        let rows: [__m512i; 8] = core::array::from_fn(|j| unsafe {
            _mm512_loadu_si512(a[j][8 * block..].as_ptr().cast())
        });
        v[8 * block..8 * block + 8].copy_from_slice(&transpose(rows));
    }
    v[24] = _mm512_setr_epi64(
        a[0][24] as i64,
        a[1][24] as i64,
        a[2][24] as i64,
        a[3][24] as i64,
        a[4][24] as i64,
        a[5][24] as i64,
        a[6][24] as i64,
        a[7][24] as i64,
    );

    keccak8_f1600(&mut v, rc);

    for block in 0..3 {
        let rows = transpose(v[8 * block..8 * block + 8].try_into().unwrap());
        for (j, row) in rows.iter().enumerate() {
            // SAFETY: as for the loads.
            unsafe { _mm512_storeu_si512(a[j][8 * block..].as_mut_ptr().cast(), *row) };
        }
    }
    let mut last = [0u64; 8];
    // SAFETY: `last` is 8 * 8 = 64 bytes, exactly the width of one `__m512i`.
    unsafe { _mm512_storeu_si512(last.as_mut_ptr().cast(), v[24]) };
    for (state, lane) in a.iter_mut().zip(last) {
        state[24] = lane;
    }
}

/// The 8x8 transpose of 64-bit elements: element `i` of vector `j` becomes
/// element `j` of vector `i`.
#[inline]
#[target_feature(enable = "avx512f")]
fn transpose(r: [__m512i; 8]) -> [__m512i; 8] {
    // Pairs of rows, interleaved: each 128-bit lane holds a 2x2 block.
    let t: [__m512i; 8] = core::array::from_fn(|i| match i % 2 {
        0 => _mm512_unpacklo_epi64(r[i], r[i + 1]),
        _ => _mm512_unpackhi_epi64(r[i - 1], r[i]),
    });
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
#[target_feature(enable = "avx512f")]
pub(super) fn keccak8_f1600(state: &mut [__m512i; 25], rc: &[u64; 24]) {
    for round_constant in rc {
        // Theta step.
        //
        // Compute the column parities C[x], then fold D[x] = C[x-1] ^ ROL(C[x+1], 1)
        // into every lane of column x.  This is fused with the rho and pi steps below.
        let c: [__m512i; 5] = core::array::from_fn(|x| {
            xor3(
                xor3(state[x], state[x + 5], state[x + 10]),
                state[x + 15],
                state[x + 20],
            )
        });
        let c_rotated: [__m512i; 5] = core::array::from_fn(|x| _mm512_rol_epi64::<1>(c[x]));

        // Rho and Pi steps.
        //
        // Rotate each lane by its rho offset and scatter it to its pi position
        // B[y, 2x + 3y] = ROL(A[x, y], RHO[x][y]).  `vprolq` takes its count
        // as an immediate, so each lane is spelled out.
        let mut b = [_mm512_setzero_si512(); 25];
        macro_rules! rho_pi {
            ($(($x:literal, $y:literal, $rho:literal)),* $(,)?) => {$(
                b[$y + 5 * ((2 * $x + 3 * $y) % 5)] = _mm512_rol_epi64::<$rho>(xor3(
                    state[$x + 5 * $y],
                    c[($x + 4) % 5],
                    c_rotated[($x + 1) % 5],
                ));
            )*};
        }
        rho_pi!(
            (0, 0, 0),
            (0, 1, 36),
            (0, 2, 3),
            (0, 3, 41),
            (0, 4, 18),
            (1, 0, 1),
            (1, 1, 44),
            (1, 2, 10),
            (1, 3, 45),
            (1, 4, 2),
            (2, 0, 62),
            (2, 1, 6),
            (2, 2, 43),
            (2, 3, 15),
            (2, 4, 61),
            (3, 0, 28),
            (3, 1, 55),
            (3, 2, 25),
            (3, 3, 21),
            (3, 4, 56),
            (4, 0, 27),
            (4, 1, 20),
            (4, 2, 39),
            (4, 3, 8),
            (4, 4, 14),
        );

        // Chi step.
        //
        // A[x, y] = B[x, y] ^ ((~B[x+1, y]) & B[x+2, y]).
        for x in 0..5 {
            for y in 0..5 {
                state[x + 5 * y] =
                    xor_andnot(b[x + 5 * y], b[(x + 1) % 5 + 5 * y], b[(x + 2) % 5 + 5 * y]);
            }
        }

        // Iota step.
        state[0] = _mm512_xor_si512(state[0], _mm512_set1_epi64(*round_constant as i64));
    }
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
