// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2id (RFC 9106), version 0x13.
//!
//! Written from RFC 9106 and the structure of its reference implementation
//! (`ref.c`'s `fill_segment` and `index_alpha`), and checked against both's
//! vectors and RustCrypto's `argon2`.

#[cfg(target_os = "none")]
use alloc::vec::Vec;

use super::blake2b::{self, Blake2b};
use crate::Error;
use crate::low::{self, Argon2Block as Block, argon2_compress};

const VERSION: u32 = 0x13;
// RFC 9106's type `y` for Argon2id.
const ARGON2ID: u32 = 2;
const SYNC_POINTS: usize = 4;
const BLOCK_BYTES: usize = 1024;
const ADDRESSES_PER_BLOCK: usize = 128;

/// Argon2id's cost, already checked against RFC 9106's limits.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Cost {
    pub(crate) memory_kib: u32,
    pub(crate) passes: u32,
    pub(crate) lanes: u32,
}

/// Fills `out`, 4 through 2^32 - 1 bytes, with Argon2id of `password` and
/// `salt` under the secret key and associated data `secret` and `data`, each
/// under 2^32 bytes.
///
/// Fails with [`Error::OutOfMemory`] if the memory `cost` asks for cannot be
/// allocated.
// Never inlined, so the MXCSR mitigation it holds covers exactly this call
// and everything it calls, as `admin/ct-vartime` counts it.
#[inline(never)]
pub(crate) fn argon2id(
    cost: Cost,
    password: &[u8],
    salt: &[u8],
    secret: &[u8],
    data: &[u8],
    out: &mut [u8],
) -> Result<(), Error> {
    // The AVX2 kernel's `vpmuludq` multiplies password-derived words.
    let _mcdt = low::Mcdt::enter();
    let lanes = cost.lanes as usize;
    // RFC 9106 rounds the memory down to a whole number of segments.
    let segment_len = cost.memory_kib as usize / (SYNC_POINTS * lanes);
    let geometry = Geometry {
        lanes: cost.lanes,
        lane_reciprocal: (u64::MAX / cost.lanes as u64).wrapping_add(1),
        passes: cost.passes,
        segment_len,
        lane_len: segment_len * SYNC_POINTS,
    };
    let blocks = geometry.lane_len * lanes;

    let mut memory = Vec::new();
    memory
        .try_reserve_exact(blocks)
        .map_err(|_| Error::OutOfMemory)?;
    memory.resize(blocks, Block::ZERO);

    let mut h = Blake2b::new(blake2b::MAX_OUT_LEN);
    for word in [
        cost.lanes,
        out.len() as u32,
        cost.memory_kib,
        cost.passes,
        VERSION,
        ARGON2ID,
        password.len() as u32,
    ] {
        h.update(&word.to_le_bytes());
    }
    h.update(password);
    for input in [salt, secret, data] {
        h.update(&(input.len() as u32).to_le_bytes());
        h.update(input);
    }
    let mut h0 = [0u8; blake2b::MAX_OUT_LEN + 8];
    h.finish(&mut h0[..blake2b::MAX_OUT_LEN]);

    let mut bytes = [0u8; BLOCK_BYTES];
    for lane in 0..cost.lanes {
        for column in 0..2u32 {
            h0[64..68].copy_from_slice(&column.to_le_bytes());
            h0[68..].copy_from_slice(&lane.to_le_bytes());
            long_hash(&[&h0], &mut bytes);
            let block = &mut memory[lane as usize * geometry.lane_len + column as usize];
            for (word, bytes) in block.0.iter_mut().zip(bytes.as_chunks::<8>().0) {
                *word = u64::from_le_bytes(*bytes);
            }
        }
    }

    for pass in 0..cost.passes {
        for slice in 0..SYNC_POINTS {
            // A slice's segments reference only each other's earlier slices,
            // so filling them one after another gives what filling them in
            // parallel would.
            for lane in 0..cost.lanes {
                geometry.fill_segment(&mut memory, pass, slice, lane);
            }
        }
    }

    // The xor of each lane's last block, indexed rather than through
    // `chunks_exact`, whose `len % chunk` the compiler folds away only in
    // some builds, so `admin/ct-vartime` would find it in others.
    let mut last = Block::ZERO;
    for lane in 1..=lanes {
        for (last, word) in last
            .0
            .iter_mut()
            .zip(&memory[lane * geometry.lane_len - 1].0)
        {
            *last ^= word;
        }
    }
    for (bytes, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(&last.0) {
        *bytes = word.to_le_bytes();
    }
    long_hash(&[&bytes], out);

    // As good as the password to an attacker, who could otherwise finish the
    // hash from it without paying for the memory.
    low::zeroise(&mut memory);
    Ok(())
}

#[derive(Clone, Copy)]
struct Geometry {
    lanes: u32,
    // 2^64 / lanes rounded up, wrapping to 0 for one lane, for `lane_of`.
    lane_reciprocal: u64,
    passes: u32,
    segment_len: usize,
    lane_len: usize,
}

impl Geometry {
    fn fill_segment(&self, memory: &mut [Block], pass: u32, slice: usize, lane: u32) {
        // Argon2id takes its first pass's first half of references from a
        // stream that depends only on public values, and the rest from the
        // memory itself.
        let independent = pass == 0 && slice < SYNC_POINTS / 2;
        let mut input = Block::ZERO;
        let mut addresses = Block::ZERO;
        if independent {
            input.0[..6].copy_from_slice(&[
                pass as u64,
                lane as u64,
                slice as u64,
                memory.len() as u64,
                self.passes as u64,
                ARGON2ID as u64,
            ]);
        }

        // The first two blocks of each lane were set from H0.
        let first = if pass == 0 && slice == 0 { 2 } else { 0 };
        if independent && first != 0 {
            next_addresses(&mut input, &mut addresses);
        }

        let lane_start = lane as usize * self.lane_len;
        for index in first..self.segment_len {
            let current = lane_start + slice * self.segment_len + index;
            let previous = match current == lane_start {
                true => lane_start + self.lane_len - 1,
                false => current - 1,
            };

            let random = match independent {
                true => {
                    if index % ADDRESSES_PER_BLOCK == 0 {
                        next_addresses(&mut input, &mut addresses);
                    }
                    addresses.0[index % ADDRESSES_PER_BLOCK]
                }
                // The one place Argon2 indexes by a secret: the leak that
                // buys its resistance to time-memory trade-offs, which
                // RFC 9106 and RFC 9807 accept, and `AGENTS.md` excepts.
                false => low::ct::into_public(memory[previous].0[0]),
            };

            let reference_lane = match pass == 0 && slice == 0 {
                true => lane,
                false => self.lane_of((random >> 32) as u32),
            };
            let reference = reference_lane as usize * self.lane_len
                + self.reference_index(pass, slice, index, random as u32, reference_lane == lane);

            let (out, previous, reference) = three(memory, current, previous, reference);
            argon2_compress(previous, reference, out, pass > 0);
        }
    }

    // `word % lanes` by Lemire, Kaser, and Kurz's "Faster remainder by direct
    // computation" (2019), exact for every 32-bit word and lane count. The
    // loop holds no division, so `admin/ct-vartime` finds only the setup's,
    // however the compiler duplicates the loop.
    fn lane_of(&self, word: u32) -> u32 {
        let fraction = self.lane_reciprocal.wrapping_mul(word as u64);
        ((fraction as u128 * self.lanes as u128) >> 64) as u32
    }

    // The reference implementation's `index_alpha`: the column `random`
    // picks, nonuniformly, from the blocks this one may reference.
    fn reference_index(
        &self,
        pass: u32,
        slice: usize,
        index: usize,
        random: u32,
        same_lane: bool,
    ) -> usize {
        // The blocks finished before this one, less the one just before it,
        // which it takes anyway, and less, in another lane, the segment
        // being filled alongside this one.
        let finished = match (pass, same_lane) {
            (0, true) => slice * self.segment_len + index - 1,
            (0, false) => slice * self.segment_len - (index == 0) as usize,
            (_, true) => self.lane_len - self.segment_len + index - 1,
            (_, false) => self.lane_len - self.segment_len - (index == 0) as usize,
        } as u64;
        let x = (random as u64 * random as u64) >> 32;
        let relative = finished - 1 - ((finished * x) >> 32);
        let start = match pass == 0 || slice == SYNC_POINTS - 1 {
            true => 0,
            false => (slice + 1) * self.segment_len,
        };
        // Below twice the lane's length, so one subtraction reduces it.
        let column = start + relative as usize;
        match column >= self.lane_len {
            true => column - self.lane_len,
            false => column,
        }
    }
}

// The next 128 data-independent references: G(0, G(0, input)), after
// counting `input` up.
fn next_addresses(input: &mut Block, addresses: &mut Block) {
    input.0[6] += 1;
    let mut once = Block::ZERO;
    argon2_compress(&Block::ZERO, input, &mut once, false);
    argon2_compress(&Block::ZERO, &once, addresses, false);
}

// Block `out` to write, and blocks `a` and `b` to read, none of them `out`.
fn three(memory: &mut [Block], out: usize, a: usize, b: usize) -> (&mut Block, &Block, &Block) {
    let (before, rest) = memory.split_at_mut(out);
    let (out_block, after) = rest.split_first_mut().unwrap();
    let (before, after): (&[Block], &[Block]) = (before, after);
    let pick = move |i: usize| match i < out {
        true => &before[i],
        false => &after[i - out - 1],
    };
    (out_block, pick(a), pick(b))
}

// RFC 9106's variable-length hash H', of `out.len()` bytes over the
// concatenation of `input`.
fn long_hash(input: &[&[u8]], out: &mut [u8]) {
    let mut h = Blake2b::new(out.len().min(blake2b::MAX_OUT_LEN));
    h.update(&(out.len() as u32).to_le_bytes());
    for input in input {
        h.update(input);
    }
    if out.len() <= blake2b::MAX_OUT_LEN {
        h.finish(out);
        return;
    }

    // Half of each 64-byte hash, each hashing the last, until the last
    // hash's whole length finishes the output.
    let mut v = [0u8; blake2b::MAX_OUT_LEN];
    h.finish(&mut v);
    let mut written = 0;
    loop {
        out[written..written + 32].copy_from_slice(&v[..32]);
        written += 32;
        if out.len() - written <= blake2b::MAX_OUT_LEN {
            break;
        }
        let mut h = Blake2b::new(blake2b::MAX_OUT_LEN);
        h.update(&v);
        h.finish(&mut v);
    }
    let mut h = Blake2b::new(out.len() - written);
    h.update(&v);
    h.finish(&mut out[written..]);
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn cost(memory_kib: u32, passes: u32, lanes: u32) -> Cost {
        Cost {
            memory_kib,
            passes,
            lanes,
        }
    }

    #[test]
    fn lane_of_is_remainder() {
        // Every lane count up to RFC 9106's limit is a 24-bit one; the words
        // straddle each multiple and power of two the reduction could slip at.
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        for lanes in (1..=64).chain([255, 256, 257, 1 << 16, (1 << 24) - 1]) {
            let geometry = Geometry {
                lanes,
                lane_reciprocal: (u64::MAX / lanes as u64).wrapping_add(1),
                passes: 1,
                segment_len: 2,
                lane_len: 8,
            };
            let edges = (0..4u32).flat_map(|k| {
                [
                    k,
                    lanes.wrapping_mul(k).wrapping_sub(1),
                    lanes.wrapping_mul(k),
                    u32::MAX - k,
                ]
            });
            let random = (0..1000).map(|_| {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (state >> 32) as u32
            });
            for word in edges.chain(random).collect::<Vec<_>>() {
                assert_eq!(geometry.lane_of(word), word % lanes, "{word} % {lanes}");
            }
        }
    }

    #[test]
    fn rfc9106_vector() {
        // RFC 9106, section 5.3.
        let mut tag = [0u8; 32];
        argon2id(
            cost(32, 3, 4),
            &[1; 32],
            &[2; 16],
            &[3; 8],
            &[4; 12],
            &mut tag,
        )
        .unwrap();
        assert_eq!(
            hex::encode(tag),
            "0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659"
        );
    }

    #[test]
    fn reference_kat() {
        // The reference implementation's `test.c`, for Argon2id version 0x13.
        for (log_memory, passes, lanes, password, salt, tag) in [
            (
                16,
                2,
                1,
                &b"password"[..],
                &b"somesalt"[..],
                "09316115d5cf24ed5a15a31a3ba326e5cf32edc24702987c02b6566f61913cf7",
            ),
            (
                18,
                2,
                1,
                b"password",
                b"somesalt",
                "78fe1ec91fb3aa5657d72e710854e4c3d9b9198c742f9616c2f085bed95b2e8c",
            ),
            (
                8,
                2,
                1,
                b"password",
                b"somesalt",
                "9dfeb910e80bad0311fee20f9c0e2b12c17987b4cac90c2ef54d5b3021c68bfe",
            ),
            (
                8,
                2,
                2,
                b"password",
                b"somesalt",
                "6d093c501fd5999645e0ea3bf620d7b8be7fd2db59c20d9fff9539da2bf57037",
            ),
            (
                16,
                1,
                1,
                b"password",
                b"somesalt",
                "f6a5adc1ba723dddef9b5ac1d464e180fcd9dffc9d1cbf76cca2fed795d9ca98",
            ),
            (
                16,
                4,
                1,
                b"password",
                b"somesalt",
                "9025d48e68ef7395cca9079da4c4ec3affb3c8911fe4f86d1a2520856f63172c",
            ),
            (
                16,
                2,
                1,
                b"differentpassword",
                b"somesalt",
                "0b84d652cf6b0c4beaef0dfe278ba6a80df6696281d7e0d2891b817d8c458fde",
            ),
            (
                16,
                2,
                1,
                b"password",
                b"diffsalt",
                "bdf32b05ccc42eb15d58fd19b1f856b113da1e9a5874fdcc544308565aa8141c",
            ),
        ] {
            let mut out = [0u8; 32];
            argon2id(
                cost(1 << log_memory, passes, lanes),
                password,
                salt,
                &[],
                &[],
                &mut out,
            )
            .unwrap();
            assert_eq!(
                hex::encode(out),
                tag,
                "m=2^{log_memory} t={passes} p={lanes}"
            );
        }
    }

    #[test]
    fn matches_rustcrypto() {
        // Memory that rounds down, lanes that do not divide it, several
        // passes, and tags around H''s 64-byte boundary and longer than a
        // block.
        for (memory_kib, passes, lanes) in
            [(8, 1, 1), (19, 2, 1), (37, 3, 3), (64, 1, 8), (300, 2, 5)]
        {
            for out_len in [4, 63, 64, 65, 96, 97, 1025] {
                let password = b"correct horse battery staple";
                let salt = b"NaCl and pepper";
                let mut ours = vec![0u8; out_len];
                argon2id(
                    cost(memory_kib, passes, lanes),
                    password,
                    salt,
                    b"key",
                    b"data",
                    &mut ours,
                )
                .unwrap();

                let params = argon2::ParamsBuilder::new()
                    .m_cost(memory_kib)
                    .t_cost(passes)
                    .p_cost(lanes)
                    .data(argon2::AssociatedData::new(b"data").unwrap())
                    .output_len(out_len)
                    .build()
                    .unwrap();
                let theirs = argon2::Argon2::new_with_secret(
                    b"key",
                    argon2::Algorithm::Argon2id,
                    argon2::Version::V0x13,
                    params,
                )
                .unwrap();
                let mut expected = vec![0u8; out_len];
                theirs
                    .hash_password_into(password, salt, &mut expected)
                    .unwrap();
                assert_eq!(
                    ours, expected,
                    "m={memory_kib} t={passes} p={lanes} T={out_len}"
                );
            }
        }
    }
}
