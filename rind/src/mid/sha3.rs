// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The SHA3 hash function and SHAKE construction.
//!
//! See <https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.202.pdf>

use crate::low::{
    Entry, sha3_keccak_f1600, sha3_keccak_nof4_f1600, sha3_keccak4_f1600, sha3_keccak4x_f1600,
};

/// A context for incremental computation of a SHA3 hash with an `R`-byte
/// rate and an `OUT`-byte digest.
#[derive(Clone)]
pub(crate) struct Sha3Context<const R: usize, const OUT: usize> {
    sponge: Sponge<R, SHA_PAD_BYTE>,
}

impl<const R: usize, const OUT: usize> Sha3Context<R, OUT> {
    /// Start a new hash computation.
    pub(crate) const fn new() -> Self {
        // FIPS 202 gives SHA3 a capacity of twice its digest length.
        const { assert!(R == 200 - 2 * OUT) };
        Self {
            sponge: Sponge::new(),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.sponge.absorb(bytes);
    }

    /// Complete the computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; OUT] {
        let mut digest = [0u8; OUT];
        SqueezingSponge::<R>::new(self.sponge.padded_state()).squeeze(&mut digest);
        digest
    }

    /// The output size of this hash.
    pub(crate) const OUTPUT_SZ: usize = OUT;
}

/// SHA3-256.
pub(crate) type Sha3_256Context = Sha3Context<{ (1600 - 512) / 8 }, 32>;

/// SHA3-384.
pub(crate) type Sha3_384Context = Sha3Context<{ (1600 - 768) / 8 }, 48>;

/// SHA3-512.
pub(crate) type Sha3_512Context = Sha3Context<{ (1600 - 1024) / 8 }, 64>;

pub(crate) type Shake128Sponge = Sponge<SHAKE_128_R_BYTES, SHAKE_PAD_BYTE>;
pub(crate) type Shake128SqueezingSponge = SqueezingSponge<SHAKE_128_R_BYTES>;
pub(crate) type Shake256Sponge = Sponge<SHAKE_256_R_BYTES, SHAKE_PAD_BYTE>;

/// SHAKE with rate `R`, read incrementally from a sponge that has absorbed
/// its input.
///
/// ML-KEM squeezes the sponges directly; ML-DSA reads through this.
pub(crate) struct Shake<const R: usize> {
    sponge: SqueezingSponge<R>,
    buffer: [u8; R],
    /// How much of `buffer` has been read: all of it until a read squeezes
    /// into it.
    buffer_offset: usize,
}

/// SHAKE128's reader, which only the tests use.
#[cfg(test)]
pub(crate) type Shake128 = Shake<SHAKE_128_R_BYTES>;

/// SHAKE256's reader.
pub(crate) type Shake256 = Shake<SHAKE_256_R_BYTES>;

impl<const R: usize> Shake<R> {
    /// Pads what `sponge` has absorbed, to read its output.
    pub(crate) fn new(sponge: &Sponge<R, SHAKE_PAD_BYTE>) -> Self {
        Self {
            sponge: sponge.finish(),
            buffer: [0; R],
            buffer_offset: R,
        }
    }

    /// Fills `output` with the next bytes of output.
    pub(crate) fn read(&mut self, output: &mut [u8]) {
        let len = output.len();
        let held = Ord::min(R - self.buffer_offset, len);
        output[..held].copy_from_slice(&self.buffer[self.buffer_offset..self.buffer_offset + held]);
        self.buffer_offset += held;
        if held == len {
            return;
        }

        // The buffer is spent: squeeze whole blocks straight into `output`,
        // and the last partial one through the buffer.
        let whole = held + (len - held) / R * R;
        self.sponge.squeeze(&mut output[held..whole]);
        if whole < len {
            self.sponge.squeeze(&mut self.buffer);
            output[whole..].copy_from_slice(&self.buffer[..len - whole]);
            self.buffer_offset = len - whole;
        }
    }
}

/// Computes `P` 128-byte SHAKE256 outputs in one go, four at a time.
///
/// Each item of `inputs` shall be 40 bytes in length, which accommodates ML-KEM's `SamplePolyCBD`
/// requirements of 33 bytes.  The 34th byte shall be `SHAKE_PAD_BYTE` and the remainder shall be
/// zeroes.
pub(crate) fn shake256_batch<const P: usize>(inputs: &[[u8; 40]; P], outputs: &mut [[u8; 128]; P]) {
    let mut states = [[0; 25]; 4];
    let mut done = 0;
    while done < P {
        let n = Ord::min(P - done, 4);
        for j in 0..n {
            debug_assert!(inputs[done + j][33] == SHAKE_PAD_BYTE);
            states[j] = padded_block::<SHAKE_256_R_BYTES>(&inputs[done + j]);
        }

        // A short batch leaves stale states in the unused lanes, whose
        // outputs are never read.
        match n {
            4 => sha3_keccak4_f1600(&mut states, &RC),
            3 => sha3_keccak_nof4_f1600::<3>(&mut states, &RC),
            2 => sha3_keccak_nof4_f1600::<2>(&mut states, &RC),
            _ => sha3_keccak_nof4_f1600::<1>(&mut states, &RC),
        }

        for j in 0..n {
            store_bytes(&states[j], &mut outputs[done + j]);
        }
        done += n;
    }
}

/// A sponge that has absorbed its input and owes a Keccak-f before each
/// output block, so a read never permutes for output it doesn't use.
pub(crate) struct SqueezingSponge<const R: usize> {
    s: [u64; 25],
}

impl<const R: usize> SqueezingSponge<R> {
    /// Resume squeezing from state `s`, which owes a Keccak-f.
    pub(crate) fn new(s: [u64; 25]) -> Self {
        Self { s }
    }

    /// Squeeze into `output`.
    pub(crate) fn squeeze(&mut self, output: &mut [u8]) {
        Entry::assert_held();
        let mut done = 0;
        while done < output.len() {
            let n = Ord::min(R, output.len() - done);
            sha3_keccak_f1600(&mut self.s, &RC);
            store_bytes(&self.s, &mut output[done..done + n]);
            done += n;
        }
    }
}

pub(crate) struct SqueezingSponge4xShake128 {
    states: [[u64; 25]; 4],
}

impl SqueezingSponge4xShake128 {
    /// Makes four new `SqueezingSponge`s by processing four SHAKE128 inputs.
    ///
    /// Each item of `input` shall be 40 bytes in length, which matches ML-KEM's requirements
    /// of 34 bytes.  The 35th byte shall be `SHAKE_PAD_BYTE` and the remainder shall be zeroes.
    pub(crate) fn new(inputs: &[[u8; 40]; 4]) -> Self {
        let mut states = [[0; 25]; 4];
        for j in 0..4 {
            debug_assert!(inputs[j][34] == SHAKE_PAD_BYTE);
            states[j] = padded_block::<SHAKE_128_R_BYTES>(&inputs[j]);
        }
        sha3_keccak4_f1600(&mut states, &RC);

        Self { states }
    }

    /// Squeezes three blocks of each sponge into `output`, returning the
    /// sponges, which then owe a Keccak-f as a `SqueezingSponge` expects.
    // Indexed rather than zipped, which Aeneas cannot translate.
    #[allow(clippy::needless_range_loop)]
    pub(crate) fn squeeze(
        mut self,
        output: &mut [[u8; SHAKE_128_R_BYTES * 3]; 4],
    ) -> [SqueezingSponge<SHAKE_128_R_BYTES>; 4] {
        // The states are post-absorb, so: squeeze, Keccak-f, squeeze,
        // Keccak-f, squeeze.
        for block in 0..3 {
            if block > 0 {
                sha3_keccak4_f1600(&mut self.states, &RC);
            }
            for j in 0..4 {
                let start = block * SHAKE_128_R_BYTES;
                store_bytes(
                    &self.states[j],
                    &mut output[j][start..start + SHAKE_128_R_BYTES],
                );
            }
        }

        self.states.map(SqueezingSponge::new)
    }
}

/// Up to four SHAKE instances with rate `R`, each over an input shorter than
/// one block, squeezed in step so their permutations run together.
pub(crate) struct Shake4x<const R: usize> {
    states: [[u64; 25]; 4],
    /// How many of `states` are in use, from one to four.
    lanes: usize,
}

/// Four SHAKE128 instances in step.
pub(crate) type Shake128x4 = Shake4x<SHAKE_128_R_BYTES>;

/// Four SHAKE256 instances in step.
pub(crate) type Shake256x4 = Shake4x<SHAKE_256_R_BYTES>;

impl<const R: usize> Shake4x<R> {
    /// Absorbs each of `inputs`, one to four of them, into its own instance.
    // Indexed rather than zipped, which Aeneas cannot translate.
    #[allow(clippy::needless_range_loop)]
    pub(crate) fn new<const LEN: usize>(inputs: &[[u8; LEN]]) -> Self {
        const { assert!(LEN < R) };
        let lanes = inputs.len();
        assert!(lanes != 0 && lanes <= 4);
        let mut states = [[0; 25]; 4];
        for j in 0..lanes {
            add_bytes(&mut states[j], 0, &inputs[j]);
            pad::<R, SHAKE_PAD_BYTE>(&mut states[j], LEN);
        }
        Self { states, lanes }
    }

    /// Squeezes the next `N` bytes of each instance into its item of
    /// `outputs`, a whole number of blocks. The items for lanes not in use
    /// are left unchanged.
    // Indexed rather than zipped, which Aeneas cannot translate.
    #[allow(clippy::needless_range_loop)]
    pub(crate) fn squeeze<const N: usize>(&mut self, outputs: &mut [[u8; N]; 4]) {
        const { assert!(N.is_multiple_of(R)) };
        Entry::assert_held();
        for block in 0..N / R {
            // A short batch leaves stale states in the unused lanes, whose
            // outputs are never written.
            match self.lanes {
                4 => sha3_keccak4_f1600(&mut self.states, &RC),
                3 => sha3_keccak_nof4_f1600::<3>(&mut self.states, &RC),
                2 => sha3_keccak_nof4_f1600::<2>(&mut self.states, &RC),
                _ => sha3_keccak_nof4_f1600::<1>(&mut self.states, &RC),
            }
            for j in 0..self.lanes {
                store_bytes(&self.states[j], &mut outputs[j][block * R..(block + 1) * R]);
            }
        }
    }
}

/// The padded SHAKE256 block of each of eight inputs, whose parts total
/// `total` bytes and agree in length, for the eight-way kernel. A short batch
/// repeats its last input.
fn pad_blocks<const P: usize>(inputs: &[[&[u8]; P]], total: usize) -> [[u8; SHAKE_256_R_BYTES]; 8] {
    const R: usize = SHAKE_256_R_BYTES;
    let mut blocks = [[0u8; R]; 8];
    for (j, block) in blocks.iter_mut().enumerate() {
        let input = &inputs[Ord::min(j, inputs.len() - 1)];
        debug_assert!(input.iter().map(|part| part.len()).sum::<usize>() == total);
        let mut at = 0;
        for part in input {
            block[at..at + part.len()].copy_from_slice(part);
            at += part.len();
        }
        block[at] = SHAKE_PAD_BYTE;
        block[R - 1] |= 0x80;
    }
    blocks
}

/// `shake256_xn` for five to eight inputs of under a block, through the
/// eight-way kernel, where the CPU has it. It returns `false`, leaving
/// `outputs` alone, where it does not or the inputs don't fit. No campaign's
/// CPU has the kernel, so `.cargo/mutants.toml` pins this function's mutants
/// and `pad_blocks` carries the logic a test can reach.
fn shake256_x8<const OUT: usize, const P: usize>(
    inputs: &[[&[u8]; P]],
    outputs: &mut [[u8; OUT]],
) -> bool {
    let total: usize = inputs[0].iter().map(|part| part.len()).sum();
    if total >= SHAKE_256_R_BYTES || OUT > 32 || !crate::low::sha3_keccak8x_available() {
        return false;
    }
    let blocks = pad_blocks(inputs, total);
    let Some(digests) = crate::low::sha3_keccak8x_hash_blocks(&blocks, &RC) else {
        return false;
    };
    for (output, digest) in outputs.iter_mut().zip(&digests[..inputs.len()]) {
        output.copy_from_slice(&digest[..OUT]);
    }
    true
}

/// SHAKE256 of each of `inputs`, one to eight, four or eight at once, writing the
/// first `OUT` bytes of each, at most a block, to its item of `outputs`.
/// Each input is its `P` parts in turn, and the inputs' parts agree in
/// length, so they absorb in place, without being copied together.
///
/// SLH-DSA hashes this way; unlike `Shake4x`, an input may span blocks.
pub(crate) fn shake256_xn<const OUT: usize, const P: usize>(
    inputs: &[[&[u8]; P]],
    outputs: &mut [[u8; OUT]],
) {
    const R: usize = SHAKE_256_R_BYTES;
    const { assert!(OUT <= R) };
    let lanes = inputs.len();
    assert!((1..=8).contains(&lanes) && outputs.len() >= lanes);
    Entry::assert_held();

    // More than four lanes: one block of eight where the CPU hashes eight at
    // once, else, as for inputs of several blocks, as two batches of up to
    // four.
    if lanes > 4 {
        if shake256_x8(inputs, outputs) {
            return;
        }
        shake256_xn(&inputs[..4], &mut outputs[..4]);
        shake256_xn(&inputs[4..], &mut outputs[4..lanes]);
        return;
    }

    // The four states interleaved, lane `i` of state `j` at `states[i][j]`,
    // which a full batch permutes in place. A short batch, which signing
    // rarely makes, moves them apart around the one-state routines, and
    // leaves stale states in the unused lanes, whose outputs are never read.
    let permute = |states: &mut [[u64; 4]; 25]| {
        if lanes == 4 {
            return sha3_keccak4x_f1600(states, &RC);
        }
        let mut apart: [[u64; 25]; 4] =
            core::array::from_fn(|j| core::array::from_fn(|i| states[i][j]));
        match lanes {
            3 => sha3_keccak_nof4_f1600::<3>(&mut apart, &RC),
            2 => sha3_keccak_nof4_f1600::<2>(&mut apart, &RC),
            _ => sha3_keccak_nof4_f1600::<1>(&mut apart, &RC),
        }
        *states = core::array::from_fn(|i| core::array::from_fn(|j| apart[j][i]));
    };
    let mut states = [[0u64; 4]; 25];
    // Inputs that fit one block, which every F, H, and PRF of SLH-DSA does:
    // each lane's padded block is built once, in order. Lengths are public.
    let total: usize = inputs[0].iter().map(|part| part.len()).sum();
    if total < R {
        let mut blocks = [[0u8; R]; 4];
        for (block, input) in blocks.iter_mut().zip(inputs) {
            debug_assert!(input.iter().map(|part| part.len()).sum::<usize>() == total);
            let mut at = 0;
            for part in input {
                block[at..at + part.len()].copy_from_slice(part);
                at += part.len();
            }
            block[at] = SHAKE_PAD_BYTE;
            block[R - 1] |= 0x80;
        }
        // Three or four lanes of at most 32 output bytes: the vectors are
        // built from the blocks and the digests read out in registers, where
        // the states below would be stored a word at a time and loaded as
        // vectors. A batch of three runs a fourth lane of the third's block.
        if OUT <= 32 && lanes >= 3 {
            blocks[3] = blocks[lanes - 1];
            if let Some(digests) = crate::low::sha3_keccak4x_hash_blocks(&blocks, &RC) {
                for (output, digest) in outputs.iter_mut().zip(&digests[..lanes]) {
                    output.copy_from_slice(&digest[..OUT]);
                }
                return;
            }
        }
        for (j, block) in blocks[..lanes].iter().enumerate() {
            for (i, word) in block.as_chunks::<8>().0.iter().enumerate() {
                states[i][j] = u64::from_le_bytes(*word);
            }
        }
        permute(&mut states);
        squeeze_x4(&states, &mut outputs[..lanes]);
        return;
    }
    // The bytes of the current block absorbed so far, under `R`.
    let mut used = 0;
    for part in 0..P {
        let len = inputs[0][part].len();
        debug_assert!(inputs.iter().all(|input| input[part].len() == len));
        let mut done = 0;
        while done < len {
            let take = Ord::min(R - used, len - done);
            for (j, input) in inputs.iter().enumerate() {
                xor_lanes(used, &input[part][done..done + take], |i, v| {
                    states[i][j] ^= v
                });
            }
            (used, done) = (used + take, done + take);
            if used == R {
                permute(&mut states);
                used = 0;
            }
        }
    }
    // The padding closes the last block, even an empty one. `j` picks a
    // state, a column of the interleaved lanes, so it indexes.
    #[allow(clippy::needless_range_loop)]
    for j in 0..lanes {
        xor_lanes(used, &[SHAKE_PAD_BYTE], |i, v| states[i][j] ^= v);
        states[R / 8 - 1][j] ^= 0x80 << 56;
    }
    permute(&mut states);

    squeeze_x4(&states, &mut outputs[..lanes]);
}

/// The first `OUT` bytes of each of `outputs`' states from the interleaved
/// `states`, state `j` into `outputs[j]`.
fn squeeze_x4<const OUT: usize>(states: &[[u64; 4]; 25], outputs: &mut [[u8; OUT]]) {
    for (j, output) in outputs.iter_mut().enumerate() {
        let (whole, tail) = output.as_chunks_mut::<8>();
        for (i, lane) in whole.iter_mut().enumerate() {
            *lane = states[i][j].to_le_bytes();
        }
        let n = tail.len();
        tail.copy_from_slice(&states[whole.len()][j].to_le_bytes()[..n]);
    }
}

/// A sponge absorbing input, XORed into the state as it arrives, so it needs
/// no buffer.
#[derive(Clone)]
pub(crate) struct Sponge<const R: usize, const PAD: u8> {
    s: [u64; 25],
    /// The bytes of the current block absorbed so far, under `R`.
    used: usize,
}

impl<const R: usize, const PAD: u8> Sponge<R, PAD> {
    pub(crate) const fn new() -> Self {
        Self { s: [0; _], used: 0 }
    }

    pub(crate) fn absorb(&mut self, bytes: &[u8]) {
        let room = R - self.used;
        if bytes.len() < room {
            add_bytes(&mut self.s, self.used, bytes);
            self.used += bytes.len();
            return;
        }

        // `digest::Context::update` leaves entering to here, so an update
        // that completes no block skips it.
        let _entry = Entry::new_secret();
        let (head, bytes) = bytes.split_at(room);
        add_bytes(&mut self.s, self.used, head);
        sha3_keccak_f1600(&mut self.s, &RC);

        let (blocks, rest) = bytes.as_chunks::<R>();
        for block in blocks {
            add_bytes(&mut self.s, 0, block);
            sha3_keccak_f1600(&mut self.s, &RC);
        }
        add_bytes(&mut self.s, 0, rest);
        self.used = rest.len();
    }

    /// Pads the input absorbed so far, to squeeze the output.
    pub(crate) fn finish(&self) -> SqueezingSponge<R> {
        SqueezingSponge::new(self.padded_state())
    }

    /// The state with the final block's padding added, owing its Keccak-f.
    fn padded_state(&self) -> [u64; 25] {
        let mut s = self.s;
        pad::<R, PAD>(&mut s, self.used);
        s
    }
}

/// Pads input absorbed `used` bytes into the state's block, under the rate
/// `R`: the domain byte `PAD`, then the rate's last bit.
fn pad<const R: usize, const PAD: u8>(s: &mut [u64; 25], used: usize) {
    add_bytes(s, used, &[PAD]);
    s[R / 8 - 1] ^= 0x80 << 56;
}

/// XORs `bytes` into the state's little-endian lanes from byte `offset`.
fn add_bytes(s: &mut [u64; 25], offset: usize, bytes: &[u8]) {
    // Up to the next lane boundary, then whole lanes, then the rest.
    let (lane, shift) = (offset / 8, offset % 8);
    let lead = Ord::min((8 - shift) % 8, bytes.len());
    let (head, bytes) = bytes.split_at(lead);
    if !head.is_empty() {
        s[lane] ^= partial_lane(head) << (8 * shift);
    }

    let first = offset.div_ceil(8);
    let (lanes, tail) = bytes.as_chunks::<8>();
    let whole = &mut s[first..first + lanes.len()];
    for (i, lane) in lanes.iter().enumerate() {
        whole[i] ^= u64::from_le_bytes(*lane);
    }
    if !tail.is_empty() {
        s[first + lanes.len()] ^= partial_lane(tail);
    }
}

/// Calls `xor(i, v)` for each lane `i` that `bytes`, placed from byte
/// `offset` of a state, touches, with `v` their little-endian value there:
/// `add_bytes` for `shake256_xn`'s interleaved states. `add_bytes` stays
/// apart, since `proofs/` reasons about its translation.
#[inline(always)]
fn xor_lanes(offset: usize, bytes: &[u8], mut xor: impl FnMut(usize, u64)) {
    // Up to the next lane boundary, then whole lanes, then the rest.
    let (lane, shift) = (offset / 8, offset % 8);
    let lead = Ord::min((8 - shift) % 8, bytes.len());
    let (head, bytes) = bytes.split_at(lead);
    if !head.is_empty() {
        xor(lane, partial_lane(head) << (8 * shift));
    }

    let first = offset.div_ceil(8);
    let (lanes, tail) = bytes.as_chunks::<8>();
    for (i, lane) in lanes.iter().enumerate() {
        xor(first + i, u64::from_le_bytes(*lane));
    }
    if !tail.is_empty() {
        xor(first + lanes.len(), partial_lane(tail));
    }
}

/// The state absorbing the one block `input`: a message, its first padding
/// byte, then zeroes, under the rate `R`, whose last bit then ends the padding.
fn padded_block<const R: usize>(input: &[u8; 40]) -> [u64; 25] {
    let mut s = [0; 25];
    add_bytes(&mut s, 0, input);
    s[R / 8 - 1] ^= 0x80 << 56;
    s
}

/// Writes the state's first `output.len()` bytes, under the rate, into
/// `output`: its lanes little-endian.
// Inlined so that a squeeze of whole blocks stores them as vectors.
#[inline(always)]
fn store_bytes(s: &[u64; 25], output: &mut [u8]) {
    let (lanes, tail) = output.as_chunks_mut::<8>();
    let whole = &s[..lanes.len()];
    // Indexed, since Aeneas cannot translate `iter_mut`.
    #[allow(clippy::needless_range_loop)]
    for i in 0..lanes.len() {
        lanes[i] = whole[i].to_le_bytes();
    }
    if !tail.is_empty() {
        let n = tail.len();
        tail.copy_from_slice(&s[lanes.len()].to_le_bytes()[..n]);
    }
}

/// `bytes`, under eight, as the low bytes of a little-endian lane.
fn partial_lane(bytes: &[u8]) -> u64 {
    let mut lane = [0u8; 8];
    lane[..bytes.len()].copy_from_slice(bytes);
    u64::from_le_bytes(lane)
}

pub(crate) const RC: [u64; 24] = [
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

pub(crate) const SHAKE_128_R_BYTES: usize = (1600 - 256) / 8;
pub(crate) const SHAKE_256_R_BYTES: usize = (1600 - 512) / 8;

/// This is 0b01_1 in keccak bit ordering.
///
/// `01` is the SHA3 domain separation constant, `1` is the multi-rate
/// padding bit.
const SHA_PAD_BYTE: u8 = 0b0000_0110;

/// This is 0b1111_1 in keccak bit ordering.
///
/// `1111` is the SHAKE domain separation constant, `1` is the multi-rate
/// padding bit.
pub(crate) const SHAKE_PAD_BYTE: u8 = 0b0001_1111;

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::*;

    /// SHAKE with rate `R` on `message`, ready to read.
    fn shake<const R: usize>(message: &[u8]) -> Shake<R> {
        let mut sponge = Sponge::new();
        sponge.absorb(message);
        Shake::new(&sponge)
    }

    #[test]
    fn sha3_256_all_lengths() {
        // see cifra `vector_length` and associated
        let mut outer = Sha3_256Context::new();

        for len in 0..1024 {
            let mut inner = Sha3_256Context::new();

            for _ in 0..len {
                inner.update(&[len as u8]);
            }

            outer.update(&inner.finish());
        }

        assert_eq!(&outer.finish(),
                   b"\xf7\xed\xf7\x2b\x34\x8c\xb4\xab\x5e\xe7\x4f\x6c\xae\xaf\x11\xad\xe2\x2f\x04\x65\x84\x8e\x5c\xaa\x14\x38\x7f\xd4\xeb\xdb\x9d\x70");
    }

    #[test]
    fn sha3_512_all_lengths() {
        let mut outer = Sha3_512Context::new();

        for len in 0..1024 {
            let mut inner = Sha3_512Context::new();

            for _ in 0..len {
                inner.update(&[len as u8]);
            }

            outer.update(&inner.finish());
        }

        assert_eq!(&outer.finish(),
                   b"\x3a\x98\x11\x17\xbc\x2f\xa3\x3b\x00\x51\x71\xf8\x80\x86\x33\x7f\x4f\x6c\xe9\xd1\x5c\xb7\x38\xc0\x9b\xe2\x8a\xb6\xd5\x38\xba\xbf\
                     \x7b\xc5\x4e\xbf\x3d\xdb\x53\x4a\x9c\x3c\x10\x85\xe7\x18\x3d\x46\xa5\x8c\xbc\xb0\x15\xb0\xdf\x50\x7a\xad\x0e\xdf\xf3\x54\x8e\xfd");
    }

    #[test]
    fn shake_incremental_read() {
        // Read SHAKE output in a big chunk, and then incrementally with a variety
        // of chunk sizes.
        //
        // The outputs must agree.
        let mut long = [0u8; 4096];
        shake::<SHAKE_128_R_BYTES>(b"hello").read(&mut long);

        let mut short = [0u8; 511];
        let mut s = shake::<SHAKE_128_R_BYTES>(b"hello");
        let mut i = 0;
        let mut len = 1;
        while (i + len) < long.len() {
            s.read(&mut short[..len]);

            assert_eq!(&long[i..i + len], &short[..len]);
            i += len;
            len = ((len + 1) * 2) % short.len();
        }
    }

    #[test]
    fn one_shot_batch_matches_single() {
        one_shot_batch_matches_single_n::<6>();
        one_shot_batch_matches_single_n::<7>();
    }

    fn one_shot_batch_matches_single_n<const P: usize>() {
        // build the 40-byte inputs in the format `one_shot_batch` requires:
        // SEED || index || SHAKE_PAD_BYTE || zeroes
        let mut inputs = [[0u8; 40]; P];
        for (n, inp) in inputs.iter_mut().enumerate() {
            inp[..32].copy_from_slice(SEED);
            inp[32] = n as u8;
            inp[33] = SHAKE_PAD_BYTE;
        }

        let mut batched = [[0u8; 128]; P];
        shake256_batch(&inputs, &mut batched);

        for (n, inp) in inputs.iter().enumerate() {
            // the absorbed message is the 33 bytes preceding the pad byte
            let mut single = [0u8; 128];
            shake::<SHAKE_256_R_BYTES>(&inp[..33]).read(&mut single);
            assert_eq!(batched[n], single);
        }
    }

    #[test]
    fn squeezing_sponge_4x_shake128_matches_single() {
        // four 40-byte inputs: SEED || i || j || SHAKE_PAD_BYTE || zeroes, with each
        // lane given a distinct message so any lane mix-up would be caught.
        let mut inputs = [[0u8; 40]; 4];
        for (n, inp) in inputs.iter_mut().enumerate() {
            inp[..32].copy_from_slice(SEED);
            inp[32] = n as u8;
            inp[33] = (n as u8) ^ 0x5a;
            inp[34] = SHAKE_PAD_BYTE;
        }

        // batched: three rate-blocks up front, then continue via the returned sponges.
        let mut batched = [[0u8; SHAKE_128_R_BYTES * 3]; 4];
        let sponges = SqueezingSponge4xShake128::new(&[inputs[0], inputs[1], inputs[2], inputs[3]])
            .squeeze(&mut batched);

        const TAIL: usize = SHAKE_128_R_BYTES * 2;
        for (n, (input, mut sponge)) in inputs.iter().zip(sponges).enumerate() {
            // single reference: absorb the 34-byte message, read the same total length.
            let mut single = [0u8; SHAKE_128_R_BYTES * 3 + TAIL];
            shake::<SHAKE_128_R_BYTES>(&input[..34]).read(&mut single);

            // the three eagerly-squeezed blocks must match
            assert_eq!(&batched[n][..], &single[..SHAKE_128_R_BYTES * 3]);

            // and squeezing on must continue the same stream
            let mut tail = [0u8; TAIL];
            sponge.squeeze(&mut tail);
            assert_eq!(&tail[..], &single[SHAKE_128_R_BYTES * 3..]);
        }
    }

    #[test]
    fn shake4x_matches_single() {
        let _entry = Entry::new_secret();
        for lanes in 1..=4 {
            let inputs: Vec<[u8; 66]> = (0..lanes)
                .map(|n| core::array::from_fn(|i| (i * 7 + n * 31) as u8))
                .collect();
            let mut x4 = Shake256x4::new(&inputs);
            let mut first = [[0u8; SHAKE_256_R_BYTES * 2]; 4];
            x4.squeeze(&mut first);
            let mut second = [[0u8; SHAKE_256_R_BYTES]; 4];
            x4.squeeze(&mut second);
            for (n, input) in inputs.iter().enumerate() {
                let mut single = [0u8; SHAKE_256_R_BYTES * 3];
                shake::<SHAKE_256_R_BYTES>(input).read(&mut single);
                assert_eq!(
                    first[n][..],
                    single[..SHAKE_256_R_BYTES * 2],
                    "{lanes} lanes"
                );
                assert_eq!(
                    second[n][..],
                    single[SHAKE_256_R_BYTES * 2..],
                    "{lanes} lanes"
                );
            }

            let inputs: Vec<[u8; 34]> = (0..lanes)
                .map(|n| core::array::from_fn(|i| (i * 3 + n * 17) as u8))
                .collect();
            let mut out = [[0u8; SHAKE_128_R_BYTES * 5]; 4];
            Shake128x4::new(&inputs).squeeze(&mut out);
            for (n, input) in inputs.iter().enumerate() {
                let mut single = [0u8; SHAKE_128_R_BYTES * 5];
                shake::<SHAKE_128_R_BYTES>(input).read(&mut single);
                assert_eq!(out[n], single, "{lanes} lanes");
            }
        }
    }

    // The eight-way kernel's input, which only AVX-512 CPUs other than Intel's
    // hash, against the one-state sponge: each padded block, absorbed into a
    // zero state and permuted once, gives its input's SHAKE256 digest.
    #[test]
    fn pad_blocks_hash_to_shake256() {
        let _entry = Entry::new_secret();
        let bytes: [u8; 200] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        for total in [0usize, 1, 40, 135] {
            for lanes in 5..=8 {
                // Each lane its own bytes, split unevenly into three parts.
                let inputs: Vec<[&[u8]; 3]> = (0..lanes)
                    .map(|j| {
                        let i = &bytes[j * 8..j * 8 + total];
                        [&i[..total / 3], &i[total / 3..total / 2], &i[total / 2..]]
                    })
                    .collect();
                let blocks = pad_blocks(&inputs, total);
                for (j, block) in blocks.iter().enumerate() {
                    let mut state = [[0u64; 25]; 4];
                    for (word, chunk) in state[0].iter_mut().zip(block.chunks_exact(8)) {
                        *word = u64::from_le_bytes(chunk.try_into().unwrap());
                    }
                    sha3_keccak_nof4_f1600::<1>(&mut state, &RC);
                    let mut digest = [0u8; 32];
                    store_bytes(&state[0], &mut digest);
                    let mut sponge = Shake256Sponge::new();
                    for part in &inputs[Ord::min(j, lanes - 1)] {
                        sponge.absorb(part);
                    }
                    let mut single = [0u8; 32];
                    Shake::new(&sponge).read(&mut single);
                    assert_eq!(digest, single, "{total} bytes, lane {j} of {lanes}");
                }
            }
        }
    }

    #[test]
    fn shake256_xn_matches_single() {
        let _entry = Entry::new_secret();
        let inputs: [[u8; 300]; 8] =
            core::array::from_fn(|n| core::array::from_fn(|i| (i * 7 + n * 31) as u8));
        for len in [0, 1, 135, 136, 137, 271, 272, 300] {
            for lanes in 1..=8 {
                // Split unevenly, so parts straddle lanes and blocks.
                let inputs: Vec<[&[u8]; 3]> = inputs[..lanes]
                    .iter()
                    .map(|i| [&i[..len / 3], &i[len / 3..len / 2], &i[len / 2..len]])
                    .collect();
                let mut outputs = [[0u8; 40]; 8];
                shake256_xn(&inputs, &mut outputs);
                for (input, output) in inputs.iter().zip(&outputs) {
                    let mut sponge = Shake256Sponge::new();
                    for part in input {
                        sponge.absorb(part);
                    }
                    let mut single = [0u8; 40];
                    Shake::new(&sponge).read(&mut single);
                    assert_eq!(*output, single, "{len} bytes, {lanes} lanes");
                }
            }
        }
    }

    // The one-block path, which three or four lanes of at most 32 output
    // bytes take through the registers on a CPU with AVX2, against the
    // one-state sponge, at the part sizes SLH-DSA hashes and at the edges of
    // one block.
    #[test]
    fn shake256_xn_one_block_matches_single() {
        fn check<const OUT: usize>(inputs: &[[u8; 400]; 8]) {
            let _entry = Entry::new_secret();
            for parts in [
                [16, 32, 16],
                [16, 32, 32],
                [24, 32, 48],
                [32, 32, 64],
                [0, 0, 0],
                [1, 1, 1],
                [40, 40, 54],
                [45, 45, 45],
            ] {
                for lanes in 1..=8 {
                    let inputs: Vec<[&[u8]; 3]> = inputs[..lanes]
                        .iter()
                        .map(|i| {
                            let (a, b) = (parts[0], parts[0] + parts[1]);
                            [&i[..a], &i[a..b], &i[b..b + parts[2]]]
                        })
                        .collect();
                    let mut outputs = [[0u8; OUT]; 8];
                    shake256_xn(&inputs, &mut outputs);
                    for (input, output) in inputs.iter().zip(&outputs) {
                        let mut sponge = Shake256Sponge::new();
                        for part in input {
                            sponge.absorb(part);
                        }
                        let mut single = [0u8; OUT];
                        Shake::new(&sponge).read(&mut single);
                        assert_eq!(*output, single, "{parts:?}, {lanes} lanes, {OUT} bytes");
                    }
                }
            }
        }
        let inputs: [[u8; 400]; 8] =
            core::array::from_fn(|n| core::array::from_fn(|i| (i * 11 + n * 37 + 5) as u8));
        check::<16>(&inputs);
        check::<24>(&inputs);
        check::<32>(&inputs);
    }

    const SEED: &[u8; 32] = b"Damn right its better than yours";

    #[test]
    fn cavp_shake() {
        #[derive(Debug)]
        enum Kind {
            None,
            Shake128,
            Shake256,
        }

        #[derive(Debug)]
        struct Cavp {
            kind: Kind,
            len: usize,
            message: Vec<u8>,
        }

        impl Default for Cavp {
            fn default() -> Self {
                Self {
                    kind: Kind::None,
                    len: 0,
                    message: Vec::new(),
                }
            }
        }

        impl CavpSink for Cavp {
            fn on_meta(&mut self, meta: &str) {
                match meta {
                    "Input Length = 128" => self.len = 16,
                    "Input Length = 256" => self.len = 32,
                    _ => {}
                }
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "COUNT" | "Outputlen" => {}
                    "Msg" => self.message = value.bytes(),
                    "Len" => self.len = (value.int() / 8) as usize,
                    "Output" => match self.kind {
                        Kind::None => {}
                        Kind::Shake128 => {
                            let mut buffer = vec![0; value.bytes().len()];
                            shake::<SHAKE_128_R_BYTES>(&self.message[..self.len]).read(&mut buffer);
                            assert_eq!(value.bytes(), buffer);
                        }
                        Kind::Shake256 => {
                            let mut buffer = vec![0; value.bytes().len()];
                            shake::<SHAKE_256_R_BYTES>(&self.message[..self.len]).read(&mut buffer);
                            assert_eq!(value.bytes(), buffer);
                        }
                    },
                    _ => {
                        todo!("{self:?} value {name} = {value:?}");
                    }
                }
            }
        }

        process_cavp(
            "../thirdparty/vectors/cavp/sha3/SHAKE128ShortMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake128,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/vectors/cavp/sha3/SHAKE128LongMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake128,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/vectors/cavp/sha3/SHAKE128VariableOut.rsp",
            &mut Cavp {
                kind: Kind::Shake128,
                ..Cavp::default()
            },
        );

        process_cavp(
            "../thirdparty/vectors/cavp/sha3/SHAKE256ShortMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake256,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/vectors/cavp/sha3/SHAKE256LongMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake256,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/vectors/cavp/sha3/SHAKE256VariableOut.rsp",
            &mut Cavp {
                kind: Kind::Shake256,
                ..Cavp::default()
            },
        );
    }
}
