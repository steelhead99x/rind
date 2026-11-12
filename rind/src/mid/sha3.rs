// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The SHA3 hash function and SHAKE construction.
//!
//! See <https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.202.pdf>

use crate::low::{Entry, sha3_keccak_f1600, sha3_keccak_nof4_f1600, sha3_keccak4_f1600};

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

/// This is SHAKE128.
///
/// This has one-shot input behaviour (all input must be provided to the
/// constructor [`Shake128::new`]) and incremental output behaviour.
///
/// ML-KEM samples through the sponges directly, so only the tests use this.
#[cfg(test)]
pub(crate) struct Shake128 {
    sponge: SqueezingSponge<SHAKE_128_R_BYTES>,
    buffer: [u8; SHAKE_128_R_BYTES],
    buffer_offset: usize,
}

#[cfg(test)]
impl Shake128 {
    /// Create a new SHAKE128 instance using `message` as input.
    ///
    /// The items of `message` are processed in order, as if concatenated.
    pub(crate) fn new(message: &[&[u8]]) -> Self {
        Self {
            sponge: Sponge::<SHAKE_128_R_BYTES, SHAKE_PAD_BYTE>::new_for_message(message),
            buffer: [0u8; SHAKE_128_R_BYTES],
            buffer_offset: SHAKE_128_R_BYTES,
        }
    }

    /// Read data from this instance into `output`.
    ///
    /// This does not fail.  It always fills `output`.
    pub(crate) fn read(&mut self, output: &mut [u8]) {
        self.sponge
            .shake_read(output, &mut self.buffer, &mut self.buffer_offset);
    }
}

pub(crate) type Shake128Sponge = Sponge<SHAKE_128_R_BYTES, SHAKE_PAD_BYTE>;
pub(crate) type Shake128SqueezingSponge = SqueezingSponge<SHAKE_128_R_BYTES>;
pub(crate) type Shake256Sponge = Sponge<SHAKE_256_R_BYTES, SHAKE_PAD_BYTE>;

/// This is SHAKE256.
///
/// This has one-shot input behaviour (all input must be provided to the
/// constructor [`Shake256::new`]) and incremental output behaviour.
///
/// ML-KEM squeezes the sponges directly; ML-DSA reads through this.
pub(crate) struct Shake256 {
    sponge: SqueezingSponge<SHAKE_256_R_BYTES>,
    buffer: [u8; SHAKE_256_R_BYTES],
    buffer_offset: usize,
}

impl Shake256 {
    /// Create a new SHAKE256 instance using `message` as input.
    ///
    /// The items of `message` are processed in order, as if concatenated.
    pub(crate) fn new(message: &[&[u8]]) -> Self {
        Self {
            sponge: Shake256Sponge::new_for_message(message),
            buffer: [0u8; SHAKE_256_R_BYTES],
            buffer_offset: SHAKE_256_R_BYTES,
        }
    }

    /// Read data from this instance into `output`.
    ///
    /// This does not fail.  It always fills `output`.
    pub(crate) fn read(&mut self, output: &mut [u8]) {
        self.sponge
            .shake_read(output, &mut self.buffer, &mut self.buffer_offset);
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

    fn shake_read(&mut self, output: &mut [u8], buffer: &mut [u8; R], buffer_offset: &mut usize) {
        let output = match *buffer_offset == buffer.len() {
            true => output,
            false => {
                let chunk = Ord::min(R - *buffer_offset, output.len());
                let (output, rest) = output.split_at_mut(chunk);
                output.copy_from_slice(&buffer[*buffer_offset..*buffer_offset + chunk]);
                *buffer_offset += chunk;
                rest
            }
        };

        if output.is_empty() {
            return;
        }

        let whole_chunks = output.len() / R;
        let (whole, tail) = output.split_at_mut(whole_chunks * R);
        self.squeeze(whole);

        if !tail.is_empty() {
            self.squeeze(buffer);
            let chunk = Ord::min(R, tail.len());
            tail.copy_from_slice(&buffer[..chunk]);
            *buffer_offset = chunk;
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
    pub(crate) fn new<const LEN: usize>(inputs: &[[u8; LEN]]) -> Self {
        const { assert!(LEN < R) };
        assert!((1..=4).contains(&inputs.len()));
        let mut states = [[0; 25]; 4];
        for (s, input) in states.iter_mut().zip(inputs) {
            add_bytes(s, 0, input);
            add_bytes(s, LEN, &[SHAKE_PAD_BYTE]);
            s[R / 8 - 1] ^= 0x80 << 56;
        }
        Self {
            states,
            lanes: inputs.len(),
        }
    }

    /// Squeezes the next `N` bytes of each instance into its item of
    /// `outputs`, a whole number of blocks. The items for lanes not in use
    /// are left with unspecified contents.
    pub(crate) fn squeeze<const N: usize>(&mut self, outputs: &mut [[u8; N]; 4]) {
        const { assert!(N.is_multiple_of(R)) };
        Entry::assert_held();
        for block in 0..N / R {
            // A short batch leaves stale states in the unused lanes, whose
            // outputs are never read.
            match self.lanes {
                4 => sha3_keccak4_f1600(&mut self.states, &RC),
                3 => sha3_keccak_nof4_f1600::<3>(&mut self.states, &RC),
                2 => sha3_keccak_nof4_f1600::<2>(&mut self.states, &RC),
                _ => sha3_keccak_nof4_f1600::<1>(&mut self.states, &RC),
            }
            for (s, output) in self.states.iter().zip(outputs.iter_mut()) {
                let output = &mut output[block * R..(block + 1) * R];
                for (ch, s) in output.as_chunks_mut::<8>().0.iter_mut().zip(s) {
                    *ch = s.to_le_bytes();
                }
            }
        }
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

    pub(crate) fn new_for_message(message: &[&[u8]]) -> SqueezingSponge<R> {
        let mut s = Self::new();
        for m in message {
            s.absorb(m);
        }
        SqueezingSponge::new(s.padded_state())
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
        add_bytes(&mut s, self.used, &[PAD]);
        s[R / 8 - 1] ^= 0x80 << 56;
        s
    }
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
fn store_bytes(s: &[u64; 25], output: &mut [u8]) {
    let mut done = 0;
    while done < output.len() {
        let n = Ord::min(8, output.len() - done);
        output[done..done + n].copy_from_slice(&s[done / 8].to_le_bytes()[..n]);
        done += n;
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
        Shake128::new(&[b"hello"]).read(&mut long);

        let mut short = [0u8; 511];
        let mut s = Shake128::new(&[b"hello"]);
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
            Shake256::new(&[&inp[..33]]).read(&mut single);
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
            Shake128::new(&[&input[..34]]).read(&mut single);

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
                Shake256::new(&[input]).read(&mut single);
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
                Shake128::new(&[input]).read(&mut single);
                assert_eq!(out[n], single, "{lanes} lanes");
            }
        }
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
                            Shake128::new(&[&self.message[..self.len]]).read(&mut buffer);
                            assert_eq!(value.bytes(), buffer);
                        }
                        Kind::Shake256 => {
                            let mut buffer = vec![0; value.bytes().len()];
                            Shake256::new(&[&self.message[..self.len]]).read(&mut buffer);
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
            "../thirdparty/cavp/sha3/SHAKE128ShortMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake128,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/cavp/sha3/SHAKE128LongMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake128,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/cavp/sha3/SHAKE128VariableOut.rsp",
            &mut Cavp {
                kind: Kind::Shake128,
                ..Cavp::default()
            },
        );

        process_cavp(
            "../thirdparty/cavp/sha3/SHAKE256ShortMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake256,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/cavp/sha3/SHAKE256LongMsg.rsp",
            &mut Cavp {
                kind: Kind::Shake256,
                ..Cavp::default()
            },
        );
        process_cavp(
            "../thirdparty/cavp/sha3/SHAKE256VariableOut.rsp",
            &mut Cavp {
                kind: Kind::Shake256,
                ..Cavp::default()
            },
        );
    }
}
