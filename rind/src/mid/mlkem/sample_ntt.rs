// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::{N, Poly, Q};
use crate::{
    low,
    mid::sha3::{self, SqueezingSponge},
};

/// FIPS-203's `SampleNTT` of each polynomial of a `K` by `K` matrix into
/// `out`, row by row, or of its transpose: eight at a time where the CPU
/// samples eight at once, then four, then one.
pub(super) fn sample_ntt(rho: &[u8; 32], transposed: bool, out: &mut [Poly]) {
    let k = super::rank(out.len());
    let mut buf = [0; 40];
    buf[..32].copy_from_slice(rho);
    buf[34] = sha3::SHAKE_PAD_BYTE;

    // Each polynomial's SHAKE128 input, row by row: `rho`, its column and row
    // indices (row and column, for the transpose), and the padding. Counting
    // rows and columns, rather than dividing, keeps division out of the code.
    let mut inputs = (0..k as u8).flat_map(|i| {
        (0..k as u8).map(move |j| {
            let mut input = buf;
            input[32..34].copy_from_slice(&match transposed {
                false => [j, i],
                true => [i, j],
            });
            input
        })
    });
    let mut next = || inputs.next().unwrap_or(buf);

    let (eights, rest) = out.as_chunks_mut::<8>();
    for outputs in eights {
        let inputs = core::array::from_fn(|_| next());
        low::mlkem_sample_poly_ntt_8x(
            &inputs,
            outputs.as_flattened_mut().try_into().unwrap(),
            _sample_poly_ntt_8x,
            _sample_poly_ntt_tail,
        );
    }

    let (fours, rest) = rest.as_chunks_mut::<4>();
    for outputs in fours {
        let inputs = core::array::from_fn(|_| next());
        sample_poly_ntt_4x(&inputs, outputs);
    }

    for output in rest {
        let input = next();
        Shake128ForMlKem::new(rho, &[input[32], input[33]]).sample_into(output);
    }
}

fn _sample_poly_ntt_8x(inputs: &[[u8; 40]; 8], outputs: &mut [i16; N * 8]) {
    let (input_quads, _) = inputs.as_chunks::<4>();
    let (output_quads, _) = outputs.as_chunks_mut::<N>().0.as_chunks_mut::<4>();
    for (inputs, outputs) in input_quads.iter().zip(output_quads.iter_mut()) {
        sample_poly_ntt_4x(inputs, outputs);
    }
}

fn sample_poly_ntt_4x(inputs: &[[u8; 40]; 4], outputs: &mut [Poly; 4]) {
    let sponge_4x = sha3::SqueezingSponge4xShake128::new(inputs);

    let mut samples = [[0; sha3::SHAKE_128_R_BYTES * 3]; 4];
    let tail_sponges = sponge_4x.squeeze(&mut samples);

    for ((output, samples), tail_sponge) in outputs.iter_mut().zip(samples.iter()).zip(tail_sponges)
    {
        let tail = Shake128ForMlKem::sample(samples, output);
        if !tail.is_empty() {
            Shake128ForMlKem {
                sponge: tail_sponge,
            }
            .tail_case(tail);
        }
    }
}

fn _sample_poly_ntt_tail(tail_sponge: &mut [u64; 25], tail: &mut [i16]) {
    Shake128ForMlKem {
        sponge: SqueezingSponge::new(*tail_sponge),
    }
    .tail_case(tail);
}

/// SHAKE128, but oriented at use in ML-KEM's `SampleNTT()`
struct Shake128ForMlKem {
    sponge: sha3::Shake128SqueezingSponge,
}

impl Shake128ForMlKem {
    /// The XOF `rho || ij`.
    fn new(rho: &[u8; 32], ij: &[u8; 2]) -> Self {
        let mut sponge = sha3::Shake128Sponge::new();
        sponge.absorb(rho);
        sponge.absorb(ij);
        Self {
            sponge: sponge.finish(),
        }
    }

    /// Extract 256 coefficients that are < Q by rejection sampling.
    ///
    /// Refer to FIPS-203 `SampleNTT()`.  This function is the inner rejection loop.
    fn sample_into(mut self, output: &mut [i16; 256]) {
        // First, we squeeze three blocks.  Each block contributes up to 112 coefficients,
        // so we get 336 candidate coefficients.
        let mut initial_bytes = [0; sha3::SHAKE_128_R_BYTES * 3];
        self.sponge.squeeze(&mut initial_bytes);

        let tail = Self::sample(&initial_bytes, output);

        // If we were unlucky, 336 candidate coeffients weren't enough.  That
        // happens with low but not negligible probability (1 in ~120).
        if !tail.is_empty() {
            self.tail_case(tail);
        }
    }

    /// Sample into `output` using the bytes `samples`
    ///
    /// Returns the _unwritten_ items in output.  Call `tail_case()` with this value if
    /// non-empty.
    #[must_use]
    fn sample<'a>(
        samples: &'_ [u8; sha3::SHAKE_128_R_BYTES * 3],
        output: &'a mut [i16; 256],
    ) -> &'a mut [i16] {
        let used = low::mlkem_rej_uniform_vartime(output, samples) as usize;
        output.split_at_mut(used).1
    }

    fn tail_case(self, output: &mut [i16]) {
        let tail_iterator = Shake128TwelveBitIterator::new(self.sponge).filter(|f| *f < Q);

        for (out, coeff) in output.iter_mut().zip(tail_iterator) {
            *out = coeff;
        }
    }
}

/// Iterates over 12-bit samples drawn from `sponge`.
struct Shake128TwelveBitIterator {
    sponge: sha3::Shake128SqueezingSponge,
    samples: [i16; Self::SAMPLE_COUNT],
    used: usize,
}

impl Shake128TwelveBitIterator {
    fn new(sponge: sha3::Shake128SqueezingSponge) -> Self {
        Self {
            sponge,
            samples: [0; Self::SAMPLE_COUNT],
            used: Self::SAMPLE_COUNT,
        }
    }

    /// Each three bytes of SHAKE output yields two coefficients.
    const SAMPLE_COUNT: usize = sha3::SHAKE_128_R_BYTES / 3 * 2;
}

impl Iterator for Shake128TwelveBitIterator {
    type Item = i16;

    #[cold]
    fn next(&mut self) -> Option<Self::Item> {
        if self.used == self.samples.len() {
            let mut bytes = [0u8; sha3::SHAKE_128_R_BYTES];
            self.sponge.squeeze(&mut bytes);

            let (chunks, _) = bytes.as_chunks::<3>();
            for (buf, d) in chunks
                .iter()
                .zip(self.samples.as_chunks_mut::<2>().0.iter_mut())
            {
                d[0] = (u16::from_le_bytes([buf[0], buf[1]]) & 0xfff) as i16;
                d[1] = (u16::from_le_bytes([buf[1], buf[2]]) >> 4) as i16;
            }
            self.used = 0;
        }

        let item = self.samples[self.used];
        self.used += 1;
        Some(item)
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // The tail rarely needs a second block, so this reads three: each three
    // bytes of every block yield two 12-bit samples.
    #[test]
    fn twelve_bit_samples_span_blocks() {
        let state: [u64; 25] =
            core::array::from_fn(|i| (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let mut bytes = [0u8; 3 * sha3::SHAKE_128_R_BYTES];
        sha3::Shake128SqueezingSponge::new(state).squeeze(&mut bytes);
        let want: Vec<i16> = bytes
            .as_chunks::<3>()
            .0
            .iter()
            .flat_map(|b| {
                let x = u32::from_le_bytes([b[0], b[1], b[2], 0]);
                [(x & 0xfff) as i16, (x >> 12) as i16]
            })
            .collect();
        let got: Vec<i16> = Shake128TwelveBitIterator::new(SqueezingSponge::new(state))
            .take(want.len())
            .collect();
        assert_eq!(got, want);
    }
}
