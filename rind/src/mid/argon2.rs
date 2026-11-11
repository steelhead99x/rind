// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2id, RFC 9106, over the backend's compression function.
//!
//! The first half of the first pass addresses memory from the pass, lane, and
//! slice, which are public. Every later block addresses it from the previous
//! block. That index is the leak RFC 9106 accepts; the arithmetic that produces
//! it does not branch on the password, and only the lane and block numbers are
//! declassified before the load. A secret-dependent address in the first half
//! is a bug: ctgrind must not see one there.

use crate::Error;
use crate::low::argon2::{Block, allocate_blocks};
use crate::low::argon2_compress as compress;
use crate::low::blake2b::{self, blake2b_long};
use crate::low::{Argon2Fill, Entry, ct, zeroise};

/// Argon2id's type id in the initial hash and the address block.
const TYPE_ID: u64 = 2;
/// RFC 9106 version 0x13.
const VERSION: u32 = 0x13;
/// Slices per pass. Lanes meet at each one.
const SYNC_POINTS: u32 = 4;
/// Reference addresses one compression of the address block produces.
const ADDRESSES_IN_BLOCK: u32 = 128;

/// Fills `out` with the Argon2id tag of `password`.
///
/// `memory_kib`, `passes`, and `lanes` are a valid parameter set.
/// `salt` is at least 8 bytes, `out` at least 4, and every length fits in a `u32`.
/// The caller holds an [`Entry`].
pub(crate) fn derive(
    password: &[u8],
    memory_kib: u32,
    passes: u32,
    lanes: u32,
    salt: &[u8],
    secret: &[u8],
    ad: &[u8],
    out: &mut [u8],
) -> Result<(), Error> {
    Entry::assert_held();
    let layout = layout(memory_kib, lanes);
    let fill = Argon2Fill::select();
    let mut memory = Matrix::allocate(layout.blocks)?;

    // H0 is BLAKE2b-512 of the parameters, not the length-prefixed H'.
    let mut h0 = [0u8; 72];
    blake2b::hash(
        &[
            &lanes.to_le_bytes(),
            &(out.len() as u32).to_le_bytes(),
            &memory_kib.to_le_bytes(),
            &passes.to_le_bytes(),
            &VERSION.to_le_bytes(),
            &(TYPE_ID as u32).to_le_bytes(),
            &(password.len() as u32).to_le_bytes(),
            password,
            &(salt.len() as u32).to_le_bytes(),
            salt,
            &(secret.len() as u32).to_le_bytes(),
            secret,
            &(ad.len() as u32).to_le_bytes(),
            ad,
        ],
        &mut h0[..64],
    );

    let mut block = [0u8; 1024];
    for lane in 0..lanes {
        for (i, counter) in [0u32, 1].into_iter().enumerate() {
            h0[64..68].copy_from_slice(&counter.to_le_bytes());
            h0[68..72].copy_from_slice(&lane.to_le_bytes());
            blake2b_long(&[&h0], &mut block);
            memory.0[lane as usize * layout.lane_length as usize + i].load(&block);
        }
    }

    let lanes_div = divisor(lanes);
    for pass in 0..passes {
        for slice in 0..SYNC_POINTS {
            for lane in 0..lanes {
                fill_segment(
                    &mut memory.0,
                    &layout,
                    &lanes_div,
                    passes,
                    pass,
                    lane,
                    slice,
                    fill,
                );
            }
        }
    }

    let mut acc = memory.0[layout.lane_length as usize - 1];
    for lane in 1..lanes {
        let last = (lane as usize + 1) * layout.lane_length as usize - 1;
        for i in 0..128 {
            acc.0[i] ^= memory.0[last].0[i];
        }
    }
    acc.store(&mut block);
    blake2b_long(&[&block], out);
    Ok(())
}

struct Matrix(Vec<Block>);

impl Matrix {
    /// One zeroed allocation. See [`allocate_blocks`] for what a refusal means,
    /// including that overcommit can kill the process instead of returning.
    fn allocate(blocks: u32) -> Result<Self, Error> {
        Ok(Self(allocate_blocks(blocks)?))
    }
}

impl Drop for Matrix {
    fn drop(&mut self) {
        // The matrix is the password hashed into 1 KiB blocks. Wipe it before
        // the allocation is freed; `zeroise` does nothing without `wipe`.
        zeroise(&mut self.0);
    }
}

struct Layout {
    blocks: u32,
    lane_length: u32,
    segment_length: u32,
}

/// RFC 9106 rounds the memory down to a multiple of `4 * lanes` blocks.
///
/// Not inlined: the division is of the public parameters, and `admin/ct-vartime`
/// lists it on this function.
#[inline(never)]
fn layout(memory_kib: u32, lanes: u32) -> Layout {
    let segment_length = memory_kib / (lanes * 4);
    Layout {
        segment_length,
        lane_length: segment_length * 4,
        blocks: segment_length * 4 * lanes,
    }
}

/// `floor(2^64 / m)` for a public modulus, so a later reduction is a multiply.
///
/// Not inlined: the division's operands are the public lane count.
#[inline(never)]
fn divisor(m: u32) -> Divisor {
    let mu = if m <= 1 {
        0
    } else {
        ((1u128 << 64) / u128::from(m)) as u64
    };
    Divisor { m, mu }
}

struct Divisor {
    m: u32,
    mu: u64,
}

/// `x % d.m`, without a division. `d.m` is public and at least 1.
fn rem_u32(x: u32, d: &Divisor) -> u32 {
    if d.m <= 1 {
        return 0;
    }
    let q = ((u128::from(x) * u128::from(d.mu)) >> 64) as u32;
    let mut r = x.wrapping_sub(q.wrapping_mul(d.m));
    // `q` can be short by one or two. The correction does not branch: a
    // borrow flag would be a secret-dependent jump when `x` is.
    r = sub_if_ge(r, d.m);
    sub_if_ge(r, d.m)
}

/// All ones when `bit` is one, else zero. `black_box` stops LLVM turning the
/// select into a conditional move, which ctgrind reports.
fn ct_mask(bit: u64) -> u64 {
    core::hint::black_box(0u64.wrapping_sub(bit))
}

/// `r - m` when `r >= m`, else `r`.
fn sub_if_ge(r: u32, m: u32) -> u32 {
    let diff = u64::from(r).wrapping_sub(u64::from(m));
    // Bit 63 is set exactly when the subtraction wrapped, which is `r < m`.
    let ge = (diff >> 63) ^ 1;
    r.wrapping_sub(m & ct_mask(ge) as u32)
}

/// `(start + relative) mod m` for a sum that is below `2 * m`.
fn reduce_below_twice(sum: u64, m: u32) -> u32 {
    let m64 = u64::from(m);
    let diff = sum.wrapping_sub(m64);
    let ge = (diff >> 63) ^ 1;
    sum.wrapping_sub(m64 & ct_mask(ge)) as u32
}

fn ct_eq(a: u32, b: u32) -> u32 {
    let x = a ^ b;
    // The high bit of `x | -x` is set exactly when `x` is not zero.
    let n = x | x.wrapping_neg();
    (n >> 31) ^ 1
}

#[allow(clippy::explicit_counter_loop)]
fn fill_segment(
    memory: &mut [Block],
    layout: &Layout,
    lanes_div: &Divisor,
    passes: u32,
    pass: u32,
    lane: u32,
    slice: u32,
    fill: Argon2Fill,
) {
    let data_independent = pass == 0 && slice < SYNC_POINTS / 2;
    let mut input = Block::zero();
    let mut address = Block::zero();
    let zero = Block::zero();
    if data_independent {
        input.0[0] = u64::from(pass);
        input.0[1] = u64::from(lane);
        input.0[2] = u64::from(slice);
        input.0[3] = u64::from(layout.blocks);
        input.0[4] = u64::from(passes);
        input.0[5] = TYPE_ID;
    }

    let mut starting = 0u32;
    if pass == 0 && slice == 0 {
        // The first two blocks of each lane were generated from H0.
        starting = 2;
        if data_independent {
            next_addresses(&mut address, &mut input, &zero, fill);
        }
    }

    let lane_length = layout.lane_length;
    let base = lane * lane_length + slice * layout.segment_length;
    let mut curr = base + starting;
    // The block before the first of a lane is the lane's last block.
    let mut prev = if slice == 0 && starting == 0 {
        base + lane_length - 1
    } else {
        curr - 1
    };

    for i in starting..layout.segment_length {
        // After the lane's last block, `prev` was incremented past the lane.
        if slice == 0 && i == 1 {
            prev = curr - 1;
        }
        let pseudo = if data_independent {
            // 128 addresses per block, a power of two, so the index is a mask.
            if i & (ADDRESSES_IN_BLOCK - 1) == 0 {
                // Words past the public counter stay zero. A password-derived
                // value written there would change the address block.
                debug_assert!(input.0[7..].iter().all(|&word| word == 0));
                next_addresses(&mut address, &mut input, &zero, fill);
            }
            address.0[(i & (ADDRESSES_IN_BLOCK - 1)) as usize]
        } else {
            memory[prev as usize].0[0]
        };

        let mut ref_lane = rem_u32((pseudo >> 32) as u32, lanes_div);
        if pass == 0 && slice == 0 {
            // No other lane has a finished block yet.
            ref_lane = lane;
        }
        let same = ct_eq(ref_lane, lane);
        let area = reference_area(pass, slice, i, layout.segment_length, lane_length, same);
        let j1 = pseudo as u32;
        let rel = (u64::from(j1) * u64::from(j1)) >> 32;
        let area64 = u64::from(area);
        // The first subtraction wraps in `u32`, as the reference does.
        // `u64` multiplication wraps, as the reference's does on a huge area.
        let relative = u64::from(area.wrapping_sub(1)).wrapping_sub(area64.wrapping_mul(rel) >> 32);
        let start = if pass != 0 && slice != SYNC_POINTS - 1 {
            (slice + 1) * layout.segment_length
        } else {
            0
        };
        let mut block_index =
            reduce_below_twice(u64::from(start).wrapping_add(relative), lane_length);

        // The data-dependent half's memory index is the accepted leak. The
        // data-independent half's index comes from the address block, built
        // only from the pass, lane, slice, and the other public parameters.
        // Those addresses are not secret, and ctgrind must not report one.
        if !data_independent {
            ref_lane = ct::into_public(ref_lane);
            block_index = ct::into_public(block_index);
        }

        let reference = memory[ref_lane as usize * lane_length as usize + block_index as usize];
        let previous = memory[prev as usize];
        let with_xor = pass != 0;
        compress(
            fill,
            &mut memory[curr as usize],
            &previous,
            &reference,
            with_xor,
        );

        curr += 1;
        prev += 1;
    }
}

/// How many blocks of this lane the reference may name, RFC 9106 section 3.4.2.
///
/// `same` is 1 when the reference lane is this lane. Both areas are computed
/// and selected, so a secret `same` does not branch.
fn reference_area(
    pass: u32,
    slice: u32,
    index: u32,
    segment: u32,
    lane_length: u32,
    same: u32,
) -> u32 {
    let (if_same, if_other) = if pass == 0 {
        if slice == 0 {
            let area = index.wrapping_sub(1);
            (area, area)
        } else {
            let base = slice.wrapping_mul(segment);
            (
                base.wrapping_add(index).wrapping_sub(1),
                if index == 0 {
                    base.wrapping_sub(1)
                } else {
                    base
                },
            )
        }
    } else {
        let base = lane_length.wrapping_sub(segment);
        (
            base.wrapping_add(index).wrapping_sub(1),
            if index == 0 {
                base.wrapping_sub(1)
            } else {
                base
            },
        )
    };
    let mask = 0u32.wrapping_sub(same);
    (if_same & mask) | (if_other & !mask)
}

fn next_addresses(address: &mut Block, input: &mut Block, zero: &Block, fill: Argon2Fill) {
    input.0[6] = input.0[6].wrapping_add(1);
    compress(fill, address, zero, input, false);
    // The second compression reads the address block it also writes.
    let reference = *address;
    compress(fill, address, zero, &reference, false);
}

impl Block {
    fn load(&mut self, bytes: &[u8; 1024]) {
        for (word, chunk) in self.0.iter_mut().zip(bytes.as_chunks::<8>().0) {
            *word = u64::from_le_bytes(*chunk);
        }
    }

    fn store(&self, bytes: &mut [u8; 1024]) {
        for (chunk, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(self.0) {
            *chunk = word.to_le_bytes();
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn remainder_matches_division() {
        for m in [1u32, 2, 3, 4, 5, 7, 8, 17, 64, 1000, 0x00FF_FFFF] {
            let d = divisor(m);
            for x in [
                0u32,
                1,
                m.saturating_sub(1),
                m,
                m.saturating_add(1),
                255,
                1024,
                u32::MAX / 2,
                u32::MAX,
            ] {
                assert_eq!(rem_u32(x, &d), x % m, "x={x} m={m}");
            }
        }
    }

    #[test]
    fn reduction_matches_modulo_below_twice() {
        for m in [8u32, 32, 1000, 1 << 20] {
            for k in 0..2 * u64::from(m) {
                assert_eq!(u64::from(reduce_below_twice(k, m)), k % u64::from(m));
            }
        }
    }

    #[test]
    fn minimum_memory_fits_eight_blocks_per_lane() {
        let layout = layout(32, 4);
        assert_eq!(layout.segment_length, 2);
        assert_eq!(layout.lane_length, 8);
        assert_eq!(layout.blocks, 32);
        assert!(Matrix::allocate(layout.blocks).is_ok());
    }
}
