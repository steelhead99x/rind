// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function G (RFC 9106, section 3.5), in portable
//! Rust.
//!
//! Written from RFC 9106. Every operation is an add, multiply, xor, or
//! rotate on 64-bit words at fixed positions, so it runs in constant time
//! wherever 32-by-32-bit multiplication does.

use alloc::vec::Vec;
use core::mem::MaybeUninit;

use crate::Error;
#[cfg(rind_backend = "x86_64")]
use crate::low::Argon2Kernel;
use crate::low::zero_bytes;

/// One 1 KiB block of Argon2's memory, as 128 little-endian words.
#[derive(Clone)]
#[repr(C, align(64))]
pub(crate) struct Argon2Block(pub(crate) [u64; 128]);

impl Argon2Block {
    pub(crate) const ZERO: Self = Self([0; 128]);
}

impl crate::low::Zeroable for Argon2Block {}

/// The block G writes: a fresh one, as the first pass fills, or one it xors
/// into, as later passes do.
pub(in crate::low) enum Argon2Out<'a> {
    Set(&'a mut MaybeUninit<Argon2Block>),
    Xor(&'a mut Argon2Block),
}

impl Argon2Kernel {
    /// G(`x`, `y`).
    pub(crate) fn g(self, x: &Argon2Block, y: &Argon2Block) -> Argon2Block {
        let mut out = MaybeUninit::uninit();
        self.compress(x, y, Argon2Out::Set(&mut out));
        // SAFETY: `Set` writes the whole block.
        unsafe { out.assume_init() }
    }
}

/// Argon2's memory: lanes of blocks, each lane set in order, as the first
/// pass does, so that none needs zeroing before it is written.
///
/// Wipes itself on drop: it is as good as the password to an attacker, who
/// could otherwise finish the hash from it without paying for the memory.
pub(crate) struct Argon2Memory {
    // Reserved, and never given a length: `set` says what is initialized.
    blocks: Vec<Argon2Block>,
    lane_len: usize,
    // How many blocks from the start of each lane are set.
    set: Vec<usize>,
}

impl Argon2Memory {
    /// Reserves `lanes` lanes of `lane_len` blocks, none of them set.
    pub(crate) fn new(lanes: usize, lane_len: usize) -> Result<Self, Error> {
        let mut blocks = Vec::new();
        let mut set = Vec::new();
        lanes
            .checked_mul(lane_len)
            .and_then(|len| blocks.try_reserve_exact(len).ok())
            .and_then(|()| set.try_reserve_exact(lanes).ok())
            .ok_or(Error::OutOfMemory)?;
        set.resize(lanes, 0);
        Ok(Self {
            blocks,
            lane_len,
            set,
        })
    }

    /// Sets `lane`'s next block to `block`.
    pub(crate) fn push(&mut self, lane: usize, block: Argon2Block) {
        let column = self.set[lane];
        assert!(column < self.lane_len);
        self.blocks.spare_capacity_mut()[lane * self.lane_len + column].write(block);
        self.set[lane] += 1;
    }

    /// Block `column` of `lane`, which must be set.
    pub(crate) fn block(&self, lane: usize, column: usize) -> &Argon2Block {
        assert!(column < self.set[lane]);
        // SAFETY: the block lies in the reservation, since `set` counts no
        // further than `lane_len` and `lane` indexed it, and is set.
        unsafe { &*self.blocks.as_ptr().add(lane * self.lane_len + column) }
    }

    /// Sets block `column` of `lane` to G of the block before it, wrapping
    /// around the lane, and block `reference`, as `(lane, column)`: setting
    /// it where it is the lane's next unset block, as the first pass does,
    /// and xoring G into it where it is set, as later passes do. Every block
    /// read must be set, and neither the one written.
    pub(crate) fn compress(
        &mut self,
        g: Argon2Kernel,
        (lane, column): (usize, usize),
        (reference_lane, reference_column): (usize, usize),
    ) {
        let previous = match column {
            0 => self.lane_len - 1,
            _ => column - 1,
        };
        let set = self.set[lane];
        assert!(column < self.lane_len && column <= set && previous < set);
        assert!(reference_column < self.set[reference_lane]);
        let at = |lane: usize, column: usize| lane * self.lane_len + column;
        let (out, previous, reference) = (
            at(lane, column),
            at(lane, previous),
            at(reference_lane, reference_column),
        );
        assert!(previous != out && reference != out);

        let (before, rest) = self.blocks.spare_capacity_mut().split_at_mut(out);
        let (out_block, after) = rest.split_first_mut().unwrap();
        let pick = |i: usize| match i < out {
            true => &before[i],
            false => &after[i - out - 1],
        };
        // SAFETY: both are set, as asserted above.
        let (previous, reference) = unsafe {
            (
                pick(previous).assume_init_ref(),
                pick(reference).assume_init_ref(),
            )
        };
        match column == set {
            true => {
                g.compress(previous, reference, Argon2Out::Set(out_block));
                self.set[lane] += 1;
            }
            // SAFETY: the block is set, since `column` is below `set`.
            false => g.compress(
                previous,
                reference,
                Argon2Out::Xor(unsafe { out_block.assume_init_mut() }),
            ),
        }
    }
}

impl Drop for Argon2Memory {
    fn drop(&mut self) {
        let reserved = self.set.len() * self.lane_len;
        // SAFETY: the reservation holds `reserved` blocks, any of whose bytes
        // may be overwritten.
        unsafe {
            zero_bytes(
                self.blocks.as_mut_ptr().cast(),
                reserved * size_of::<Argon2Block>(),
            )
        };
    }
}

/// The portable G, where no faster one runs.
#[cfg(not(rind_backend = "x86_64"))]
#[derive(Clone, Copy)]
pub(crate) struct Argon2Kernel;

#[cfg(not(rind_backend = "x86_64"))]
impl Argon2Kernel {
    /// The fastest G this CPU runs, picked once so no block checks again.
    pub(crate) fn new() -> Self {
        Self
    }

    /// Writes G(`x`, `y`) to `out`.
    #[inline(always)]
    pub(in crate::low) fn compress(self, x: &Argon2Block, y: &Argon2Block, out: Argon2Out<'_>) {
        argon2_compress(x, y, out)
    }
}

/// Writes G(`x`, `y`) to `out`.
#[inline(always)]
pub(crate) fn argon2_compress(x: &Argon2Block, y: &Argon2Block, out: Argon2Out<'_>) {
    let r = Argon2Block(core::array::from_fn(|i| x.0[i] ^ y.0[i]));
    let mut q = r.clone();

    // P over each row of sixteen consecutive words, then over each column of
    // eight pairs of words, a row's length apart.
    for row in 0..8 {
        permute(&mut q, |v| 16 * row + v);
    }
    for column in 0..8 {
        permute(&mut q, |v| 2 * column + (v & 1) + (v / 2) * 16);
    }

    match out {
        // Written word by word rather than moved in whole, which would copy
        // the block once more.
        Argon2Out::Set(out) => {
            let out = out.as_mut_ptr().cast::<u64>();
            for i in 0..128 {
                // SAFETY: the block is 128 words, any of which may be written.
                unsafe { out.add(i).write(q.0[i] ^ r.0[i]) };
            }
        }
        Argon2Out::Xor(out) => {
            for i in 0..128 {
                out.0[i] ^= q.0[i] ^ r.0[i];
            }
        }
    }
}

// RFC 9106's P, over the sixteen words of `block` that `at` maps 0 through
// 15 to.
#[inline(always)]
fn permute(block: &mut Argon2Block, at: impl Fn(usize) -> usize) {
    let words = &mut block.0;
    let mut v = [0u64; 16];
    for (i, v) in v.iter_mut().enumerate() {
        *v = words[at(i)];
    }
    gb(&mut v, 0, 4, 8, 12);
    gb(&mut v, 1, 5, 9, 13);
    gb(&mut v, 2, 6, 10, 14);
    gb(&mut v, 3, 7, 11, 15);
    gb(&mut v, 0, 5, 10, 15);
    gb(&mut v, 1, 6, 11, 12);
    gb(&mut v, 2, 7, 8, 13);
    gb(&mut v, 3, 4, 9, 14);
    for (i, v) in v.iter().enumerate() {
        words[at(i)] = *v;
    }
}

// RFC 9106's GB: BLAKE2b's G with each addition `a + b` replaced by
// `a + b + 2 * lo(a) * lo(b)`, and no message words.
#[inline(always)]
fn gb(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize) {
    v[a] = fbla(v[a], v[b]);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = fbla(v[c], v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = fbla(v[a], v[b]);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = fbla(v[c], v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

#[inline(always)]
fn fbla(x: u64, y: u64) -> u64 {
    // Wrapping: a 32x32-bit product cannot overflow, but a debug build's
    // overflow check would still branch on the secret operands.
    let product = (x as u32 as u64).wrapping_mul(y as u32 as u64);
    x.wrapping_add(y).wrapping_add(product.wrapping_mul(2))
}
