// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA1, for legacy protocols only.
//!
//! SHA1 is described in [FIPS180](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
//! Its collision resistance is broken, so it must not be used where that
//! matters, such as in signatures.

use crate::low::{Blockwise, Entry, UpdateBlocks};

/// SHA1's chaining value after a whole number of blocks.
///
/// Finishing needs no buffer, so a one-shot hash, or HMAC from its keyed
/// states, works on this alone.
#[derive(Clone, Copy)]
pub(crate) struct Sha1State {
    h: [u32; 5],
    // u64 so 32-bit targets can hash past 4 GiB.
    nblocks: u64,
}

impl Sha1State {
    /// SHA1's initial value.
    pub(crate) const fn new() -> Self {
        Self {
            h: [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0],
            nblocks: 0,
        }
    }

    fn compress(h: &mut [u32; 5], blocks: &[u8]) {
        Entry::assert_held();
        crate::low::sha1_compress_blocks(h, blocks);
    }

    /// The hash of the input so far followed by `message`, leaving this state as it was.
    pub(crate) fn finish_with(&self, message: &[u8]) -> [u8; Sha1Context::OUTPUT_SZ] {
        const BLOCK_SZ: usize = Sha1Context::BLOCK_SZ;
        let bits = self
            .nblocks
            .checked_mul(BLOCK_SZ as u64)
            .and_then(|bytes| bytes.checked_add(message.len() as u64))
            .and_then(|bytes| bytes.checked_mul(8))
            .expect("excess data processed by hash function");

        // Copies `h` alone: copying the whole state can leave it straddling
        // two stores, which the SHA extensions' 16-byte load of it then
        // waits on instead of forwarding.
        let mut h = self.h;
        Entry::assert_held();
        crate::low::sha1_compress_padded(&mut h, message, bits.to_be_bytes());

        // Indexes rather than zipping `as_chunks_mut`, which Aeneas cannot
        // translate, so `proofs/` can prove the encoding.
        let mut r = [0u8; Sha1Context::OUTPUT_SZ];
        for (i, word) in h.iter().enumerate() {
            r[i * 4..(i + 1) * 4].copy_from_slice(&word.to_be_bytes());
        }
        r
    }
}

impl UpdateBlocks for Sha1State {
    fn update_blocks(&mut self, blocks: &[u8]) {
        debug_assert!(blocks.len().is_multiple_of(Sha1Context::BLOCK_SZ));
        if !blocks.is_empty() {
            // `digest::Context::update` and `hmac::Context::update` leave
            // entering to here.
            let _entry = Entry::new_secret();
            Self::compress(&mut self.h, blocks);
            self.nblocks = self
                .nblocks
                .saturating_add((blocks.len() / Sha1Context::BLOCK_SZ) as u64);
        }
    }
}

/// A context for incremental computation of SHA1.
#[derive(Clone, Copy)]
pub(crate) struct Sha1Context {
    state: Sha1State,
    blockwise: Blockwise<{ Self::BLOCK_SZ }>,
}

impl Sha1Context {
    /// Start a new SHA1 hash computation.
    pub(crate) const fn new() -> Self {
        Self::resume(Sha1State::new())
    }

    /// Continue a hash computation from `state`.
    pub(crate) const fn resume(state: Sha1State) -> Self {
        Self {
            state,
            blockwise: Blockwise::new(),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    #[inline(always)]
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.blockwise.update(bytes, &mut self.state);
    }

    /// Complete the SHA1 computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; Self::OUTPUT_SZ] {
        self.state.finish_with(self.blockwise.buffered())
    }

    /// The internal block size of SHA1.
    pub(crate) const BLOCK_SZ: usize = 64;

    /// The output size of SHA1.
    pub(crate) const OUTPUT_SZ: usize = 20;
}

#[cfg(test)]
mod tests {
    use super::*;

    // The bit length overflows a 32-bit usize at 512 MiB, and the byte count
    // at 4 GiB.
    #[test]
    fn length_past_32_bit_usize() {
        for bytes in [1u64 << 29, 1 << 32] {
            let mut ctx = Sha1Context::new();
            ctx.state.nblocks = bytes / Sha1Context::BLOCK_SZ as u64;
            ctx.update(b"x");
            ctx.finish();
        }
    }
}
