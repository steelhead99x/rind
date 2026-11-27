// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// The loops here count indices, rather than zip iterators or call closures,
// since their proof is about Aeneas's translation, which takes neither.
#![allow(
    clippy::needless_range_loop,
    reason = "Aeneas translates no iterator adapter"
)]

use super::{N, Poly, Q};
use crate::{low, mid::sha3};

/// FIPS-203's `SampleNTT` of each polynomial of a `K` by `K` matrix into
/// `out`, row by row, or of its transpose: eight at a time where the CPU
/// samples eight at once (but for ML-KEM-768), then four, then one.
pub(super) fn sample_ntt(rho: &[u8; 32], transposed: bool, out: &mut [Poly]) {
    let k = super::rank(out.len());

    // ML-KEM-768 never samples eight at a time: it takes eight of its nine
    // polynomials four at a time, over the four-way SHAKE128 `proofs/`
    // proves, and the ninth alone, so Graviola's unproven eight-way Keccak is
    // off its path. Where that would run, ML-KEM-768 runs
    // pyca/verified-garbage's routines instead, so this costs nothing
    // measurable. Only x86_64 has an eight-way sampler, and only
    // ML-KEM-1024's sixteen polynomials split into eights.
    #[cfg(rind_backend = "x86_64")]
    if k == 4 {
        sample_ntt_8x(rho, transposed, out);
        return;
    }

    // Each polynomial's SHAKE128 input, row by row: `rho`, its column and row
    // indices (row and column, for the transpose), and the padding. Counting
    // rows and columns, rather than dividing, keeps division out of the code.
    let (mut i, mut j) = (0, 0);
    let mut done = 0;
    while done + 4 <= out.len() {
        let mut inputs = [[0; 40]; 4];
        for input in 0..4 {
            inputs[input] = shake_input(rho, transposed, i, j);
            (i, j) = next_index(k, i, j);
        }
        let outputs = (&mut out[done..done + 4]).try_into().unwrap();
        sample_poly_ntt_4x(&inputs, outputs);
        done += 4;
    }

    while done < out.len() {
        let input = shake_input(rho, transposed, i, j);
        (i, j) = next_index(k, i, j);
        let mut sponge = sha3::Shake128Sponge::new();
        sponge.absorb(&input[..34]);
        sample_into(sponge.finish(), &mut out[done]);
        done += 1;
    }
}

/// The SHAKE128 input of the polynomial in row `i` and column `j`: `rho`,
/// then `j` and `i`, or `i` and `j` for the transpose, then the padding.
fn shake_input(rho: &[u8; 32], transposed: bool, i: u8, j: u8) -> [u8; 40] {
    let mut input = [0; 40];
    input[..32].copy_from_slice(rho);
    if transposed {
        input[32] = i;
        input[33] = j;
    } else {
        input[32] = j;
        input[33] = i;
    }
    input[34] = sha3::SHAKE_PAD_BYTE;
    input
}

/// The row and column after row `i` and column `j` of a `k` by `k` matrix.
fn next_index(k: usize, i: u8, j: u8) -> (u8, u8) {
    if j as usize + 1 == k {
        (i + 1, 0)
    } else {
        (i, j + 1)
    }
}

/// [`sample_ntt`] of ML-KEM-1024's matrix, eight polynomials at a time on
/// x86_64's eight-way sampler where the CPU has it.
#[cfg(rind_backend = "x86_64")]
fn sample_ntt_8x(rho: &[u8; 32], transposed: bool, out: &mut [Poly]) {
    let (mut i, mut j) = (0, 0);
    let (eights, _) = out.as_chunks_mut::<8>();
    for outputs in eights {
        let mut inputs = [[0; 40]; 8];
        for input in &mut inputs {
            *input = shake_input(rho, transposed, i, j);
            (i, j) = next_index(4, i, j);
        }
        let outputs = outputs.as_flattened_mut().try_into().unwrap();
        // The eight-way sampler hands back the tails.
        low::mlkem_sample_poly_ntt_8x(&inputs, outputs, sample_poly_ntt_8x, sample_poly_ntt_tail);
    }
}

#[cfg(rind_backend = "x86_64")]
fn sample_poly_ntt_8x(inputs: &[[u8; 40]; 8], outputs: &mut [i16; N * 8]) {
    let (input_quads, _) = inputs.as_chunks::<4>();
    let (output_quads, _) = outputs.as_chunks_mut::<N>().0.as_chunks_mut::<4>();
    for (inputs, outputs) in input_quads.iter().zip(output_quads.iter_mut()) {
        sample_poly_ntt_4x(inputs, outputs);
    }
}

#[cfg(rind_backend = "x86_64")]
fn sample_poly_ntt_tail(tail_sponge: &mut [u64; 25], tail: &mut [i16]) {
    tail_case(&mut sha3::SqueezingSponge::new(*tail_sponge), tail);
}

fn sample_poly_ntt_4x(inputs: &[[u8; 40]; 4], outputs: &mut [Poly; 4]) {
    let sponge_4x = sha3::SqueezingSponge4xShake128::new(inputs);

    let mut samples = [[0; sha3::SHAKE_128_R_BYTES * 3]; 4];
    let mut tail_sponges = sponge_4x.squeeze(&mut samples);

    for poly in 0..4 {
        sample_from(&samples[poly], &mut tail_sponges[poly], &mut outputs[poly]);
    }
}

/// Extract 256 coefficients that are < Q from `sponge` by rejection
/// sampling: FIPS-203's `SampleNTT()` loop.
fn sample_into(mut sponge: sha3::Shake128SqueezingSponge, output: &mut Poly) {
    // First, we squeeze three blocks.  Each block contributes up to 112 coefficients,
    // so we get 336 candidate coefficients.
    let mut samples = [0; sha3::SHAKE_128_R_BYTES * 3];
    sponge.squeeze(&mut samples);
    sample_from(&samples, &mut sponge, output);
}

/// Sample into `output` from `samples`, the sponge's first three blocks,
/// then from `sponge`, which continues after them, if 336 candidates were
/// not enough. That happens with low but not negligible probability (1 in
/// ~120).
fn sample_from(
    samples: &[u8; sha3::SHAKE_128_R_BYTES * 3],
    sponge: &mut sha3::Shake128SqueezingSponge,
    output: &mut Poly,
) {
    let used = low::mlkem_rej_uniform_vartime(output, samples) as usize;
    if used < N {
        tail_case(sponge, &mut output[used..]);
    }
}

/// Fill `output` with the 12-bit samples below Q drawn from `sponge`, a
/// block at a time: each three bytes yield two samples, the low 12 bits
/// first.
#[cold]
fn tail_case(sponge: &mut sha3::Shake128SqueezingSponge, output: &mut [i16]) {
    let mut done = 0;
    while done < output.len() {
        let mut bytes = [0u8; sha3::SHAKE_128_R_BYTES];
        sponge.squeeze(&mut bytes);
        for t in 0..sha3::SHAKE_128_R_BYTES / 3 {
            let (b0, b1, b2) = (bytes[3 * t], bytes[3 * t + 1], bytes[3 * t + 2]);
            let d1 = (u16::from_le_bytes([b0, b1]) & 0xfff) as i16;
            let d2 = (u16::from_le_bytes([b1, b2]) >> 4) as i16;
            if d1 < Q && done < output.len() {
                output[done] = d1;
                done += 1;
            }
            if d2 < Q && done < output.len() {
                output[done] = d2;
                done += 1;
            }
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // The tail rarely needs a second block, so this takes more samples than
    // two blocks can hold, 224: each three bytes of every block yield two
    // 12-bit samples, of which those below Q are kept.
    #[test]
    fn tail_samples_span_blocks() {
        let state: [u64; 25] =
            core::array::from_fn(|i| (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let mut bytes = [0u8; 4 * sha3::SHAKE_128_R_BYTES];
        sha3::Shake128SqueezingSponge::new(state).squeeze(&mut bytes);
        let want: Vec<i16> = bytes
            .as_chunks::<3>()
            .0
            .iter()
            .flat_map(|b| {
                let x = u32::from_le_bytes([b[0], b[1], b[2], 0]);
                [(x & 0xfff) as i16, (x >> 12) as i16]
            })
            .filter(|&d| d < Q)
            .take(240)
            .collect();
        let mut got = vec![0; want.len()];
        tail_case(&mut sha3::SqueezingSponge::new(state), &mut got);
        assert_eq!(got, want);
    }
}
