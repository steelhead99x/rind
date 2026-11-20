// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM's PRF, SHAKE256 of a 33-byte input for 128 bytes, on eight inputs
//! at once in zmm registers: Graviola's `sha3_shake256_8x_one_block`, over
//! the eight-way Keccak-f[1600] its SampleNTT runs (see
//! `mlkem_sample_poly_ntt_8x`). Each input fills less than one block and its
//! output less than one, so one permutation serves all eight.

use core::arch::x86_64::*;

use super::cpu::HaveAvx512ForMlKem;
use super::mlkem_sample_poly_ntt_8x::{_sha3_keccak8_f1600, RC};

/// Computes the first `count` of eight 128-byte PRF outputs.
type Fallback = fn(&[[u8; 40]; 8], &mut [[u8; 128]; 8], usize);

/// SHAKE256 of each of `inputs`, which are padded already but for the last
/// byte of the block, into `outputs`. The first `count` are wanted;
/// `fallback_fn` computes those where the CPU lacks AVX-512.
pub(crate) fn mlkem_shake256_8x(
    inputs: &[[u8; 40]; 8],
    outputs: &mut [[u8; 128]; 8],
    count: usize,
    fallback_fn: Fallback,
) {
    match HaveAvx512ForMlKem::check() {
        // SAFETY: the token proves AVX-512 F, which is all this uses.
        Some(proof) => unsafe { shake256_8x_avx512(inputs, outputs, proof) },
        None => fallback_fn(inputs, outputs, count),
    }
}

#[target_feature(enable = "avx512f")]
fn shake256_8x_avx512(
    inputs: &[[u8; 40]; 8],
    outputs: &mut [[u8; 128]; 8],
    _proof: HaveAvx512ForMlKem,
) {
    // Built transposed: `states[word]` holds `word` of all eight states.
    // Only the first five words of each input can be nonzero.
    let mut states = [_mm512_setzero_si512(); 25];
    let word =
        |lane: usize, w: usize| u64::from_le_bytes(inputs[lane].as_chunks::<8>().0[w]) as i64;
    for (w, state) in states[..5].iter_mut().enumerate() {
        *state = _mm512_setr_epi64(
            word(0, w),
            word(1, w),
            word(2, w),
            word(3, w),
            word(4, w),
            word(5, w),
            word(6, w),
            word(7, w),
        );
    }
    // The pad's final bit, at the end of SHAKE256's 136-byte rate.
    states[16] = _mm512_set1_epi64(0x8000_0000_0000_0000_u64 as i64);

    _sha3_keccak8_f1600(&mut states, &RC);

    // The 128 output bytes are the first 16 words of each state.
    let low = transpose_8x8(states[..8].try_into().unwrap());
    let high = transpose_8x8(states[8..16].try_into().unwrap());
    for (output, (low, high)) in outputs.iter_mut().zip(low.iter().zip(&high)) {
        let (halves, _) = output.as_chunks_mut::<64>();
        // SAFETY: each half is 64 bytes, exactly the width of one `__m512i`.
        unsafe {
            _mm512_storeu_si512(halves[0].as_mut_ptr().cast(), *low);
            _mm512_storeu_si512(halves[1].as_mut_ptr().cast(), *high);
        }
    }
}

/// Transposes an 8x8 matrix of 64-bit words, held as eight rows.
#[target_feature(enable = "avx512f")]
fn transpose_8x8(r: [__m512i; 8]) -> [__m512i; 8] {
    // Pairs of rows interleaved: a[0] = r0[0] r1[0] r0[2] r1[2] r0[4] r1[4] r0[6] r1[6], and so on.
    let a = [
        _mm512_unpacklo_epi64(r[0], r[1]),
        _mm512_unpackhi_epi64(r[0], r[1]),
        _mm512_unpacklo_epi64(r[2], r[3]),
        _mm512_unpackhi_epi64(r[2], r[3]),
        _mm512_unpacklo_epi64(r[4], r[5]),
        _mm512_unpackhi_epi64(r[4], r[5]),
        _mm512_unpacklo_epi64(r[6], r[7]),
        _mm512_unpackhi_epi64(r[6], r[7]),
    ];

    // 128-bit pairs gathered: b[0] = r0[0] r1[0] r0[4] r1[4] r2[0] r3[0] r2[4] r3[4], and so on.
    let b = [
        _mm512_shuffle_i64x2::<0x88>(a[0], a[2]),
        _mm512_shuffle_i64x2::<0xdd>(a[0], a[2]),
        _mm512_shuffle_i64x2::<0x88>(a[1], a[3]),
        _mm512_shuffle_i64x2::<0xdd>(a[1], a[3]),
        _mm512_shuffle_i64x2::<0x88>(a[4], a[6]),
        _mm512_shuffle_i64x2::<0xdd>(a[4], a[6]),
        _mm512_shuffle_i64x2::<0x88>(a[5], a[7]),
        _mm512_shuffle_i64x2::<0xdd>(a[5], a[7]),
    ];

    [
        _mm512_shuffle_i64x2::<0x88>(b[0], b[4]),
        _mm512_shuffle_i64x2::<0x88>(b[2], b[6]),
        _mm512_shuffle_i64x2::<0x88>(b[1], b[5]),
        _mm512_shuffle_i64x2::<0x88>(b[3], b[7]),
        _mm512_shuffle_i64x2::<0xdd>(b[0], b[4]),
        _mm512_shuffle_i64x2::<0xdd>(b[2], b[6]),
        _mm512_shuffle_i64x2::<0xdd>(b[1], b[5]),
        _mm512_shuffle_i64x2::<0xdd>(b[3], b[7]),
    ]
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::x86_64::adx_mux::tests::Rng;
    use crate::low::x86_64::ct_sde;
    use crate::mid::sha3;

    fn inputs(rng: &mut Rng) -> [[u8; 40]; 8] {
        let sigma: [u8; 32] = core::array::from_fn(|_| rng.next() as u8);
        core::array::from_fn(|n| {
            let mut input = [0; 40];
            input[..32].copy_from_slice(&sigma);
            input[32] = n as u8;
            input[33] = sha3::SHAKE_PAD_BYTE;
            input
        })
    }

    // Against SHAKE256 one input at a time, under a seed `admin/ctgrind` keeps
    // secret: valgrind cannot run AVX-512, so only where the CPU lacks it does
    // this reach the fallback, which `ct_sde_mlkem_prf_8x` stands in for.
    #[test]
    fn matches_shake256() {
        let mut rng = Rng(7);
        for _ in 0..8 {
            let inputs = inputs(&mut rng);
            ct::secret_slice(inputs.as_flattened());
            let mut ours = [[0; 128]; 8];
            mlkem_shake256_8x(&inputs, &mut ours, 8, |inputs, outputs, count| {
                for (input, output) in inputs.iter().zip(outputs.iter_mut()).take(count) {
                    sha3::shake256_batch::<1>(&[*input], core::array::from_mut(output));
                }
            });
            for (input, ours) in inputs.iter().zip(ours) {
                let mut want = [[0; 128]];
                sha3::shake256_batch::<1>(&[*input], &mut want);
                assert_eq!(ct::into_public(ours), ct::into_public(want[0]));
            }
        }
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_mlkem_prf_8x() {
        let mut rng = Rng(ct_sde::seed());
        let proof = HaveAvx512ForMlKem::check().expect("AVX-512 for ML-KEM");
        let inputs = inputs(&mut rng);
        let mut outputs = [[0; 128]; 8];
        // SAFETY: the token proves AVX-512 F.
        ct_sde::traced(|| unsafe { shake256_8x_avx512(&inputs, &mut outputs, proof) });
    }
}
