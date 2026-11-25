// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! MD5, for legacy protocols only.
//!
//! MD5 is described in [RFC 1321](https://www.rfc-editor.org/rfc/rfc1321).
//! Its collision resistance is broken, so it must not be used where that
//! matters, such as in signatures.

use crate::low::{Blockwise, Entry, UpdateBlocks, md5_compress_blocks, pad, split_tail};

/// MD5's chaining value after a whole number of blocks.
#[derive(Clone, Copy)]
pub(crate) struct Md5State {
    h: [u32; 4],
    // u64 so 32-bit targets can hash past 4 GiB; only its low 58 bits count.
    nblocks: u64,
}

impl Md5State {
    /// MD5's initial value.
    pub(crate) const fn new() -> Self {
        Self {
            h: [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476],
            nblocks: 0,
        }
    }

    /// The hash of the input so far followed by `message`, leaving this state as it was.
    pub(crate) fn finish_with(&self, message: &[u8]) -> [u8; Md5Context::OUTPUT_SZ] {
        const BLOCK_SZ: usize = Md5Context::BLOCK_SZ;
        // RFC 1321 closes the message with its bit length modulo 2^64, so a
        // longer one is still a message.
        let bits = self
            .nblocks
            .wrapping_mul(BLOCK_SZ as u64 * 8)
            .wrapping_add((message.len() as u64).wrapping_mul(8));

        let mut h = self.h;
        Entry::assert_held();
        let (blocks, rest) = split_tail::<BLOCK_SZ, 8>(message);
        md5_compress_blocks(&mut h, blocks);
        let mut last = [[0u8; BLOCK_SZ]; 2];
        md5_compress_blocks(&mut h, pad(rest, bits.to_le_bytes(), &mut last));

        let mut r = [0u8; Md5Context::OUTPUT_SZ];
        for (i, word) in h.iter().enumerate() {
            r[i * 4..(i + 1) * 4].copy_from_slice(&word.to_le_bytes());
        }
        r
    }
}

impl UpdateBlocks for Md5State {
    fn update_blocks(&mut self, blocks: &[u8]) {
        debug_assert!(blocks.len().is_multiple_of(Md5Context::BLOCK_SZ));
        if !blocks.is_empty() {
            // `digest::Context::update` leaves entering to here.
            let _entry = Entry::new_secret();
            md5_compress_blocks(&mut self.h, blocks);
            self.nblocks = self
                .nblocks
                .wrapping_add((blocks.len() / Md5Context::BLOCK_SZ) as u64);
        }
    }
}

/// A context for incremental computation of MD5.
#[derive(Clone, Copy)]
pub(crate) struct Md5Context {
    state: Md5State,
    blockwise: Blockwise<{ Self::BLOCK_SZ }>,
}

impl Md5Context {
    /// Start a new MD5 hash computation.
    pub(crate) const fn new() -> Self {
        Self {
            state: Md5State::new(),
            blockwise: Blockwise::new(),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    #[inline(always)]
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.blockwise.update(bytes, &mut self.state);
    }

    /// Complete the MD5 computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; Self::OUTPUT_SZ] {
        self.state.finish_with(self.blockwise.buffered())
    }

    /// The internal block size of MD5.
    pub(crate) const BLOCK_SZ: usize = 64;

    /// The output size of MD5.
    pub(crate) const OUTPUT_SZ: usize = 16;
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // RFC 1321's test suite, appendix A.5.
    #[test]
    fn rfc1321() {
        for (message, digest) in [
            ("", "d41d8cd98f00b204e9800998ecf8427e"),
            ("a", "0cc175b9c0f1b6a831c399e269772661"),
            ("abc", "900150983cd24fb0d6963f7d28e17f72"),
            ("message digest", "f96b697d7cb7938d525a2f31aaf161d0"),
            (
                "abcdefghijklmnopqrstuvwxyz",
                "c3fcd3d76192e4007dfb496cca67e13b",
            ),
            (
                "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
                "d174ab98d277d9f5a5611c2c9f419d9f",
            ),
            (
                "12345678901234567890123456789012345678901234567890123456789012345678901234567890",
                "57edf4a22be3c955ac49da2e2107b67a",
            ),
        ] {
            let mut ctx = Md5Context::new();
            ctx.update(message.as_bytes());
            assert_eq!(hex::encode(ctx.finish()), digest, "{message:?}");
        }
    }

    // The bit length overflows a 32-bit usize at 512 MiB, and the byte count
    // at 4 GiB.
    #[test]
    fn length_past_32_bit_usize() {
        for bytes in [1u64 << 29, 1 << 32] {
            let mut ctx = Md5Context::new();
            ctx.state.nblocks = bytes / Md5Context::BLOCK_SZ as u64;
            ctx.update(b"x");
            ctx.finish();
        }
    }

    // Past 2^64 bits the length wraps, as RFC 1321 specifies, rather than
    // panicking: 2^58 more blocks hash as none.
    #[test]
    fn length_wraps_at_2_64_bits() {
        // `update` holds the last whole block back, so compresses one here.
        let mut ctx = Md5Context::new();
        ctx.state.nblocks = u64::MAX;
        ctx.update(&[0x61; 2 * Md5Context::BLOCK_SZ]);
        assert_eq!(ctx.state.nblocks, 0);

        let mut wrapped = Md5Context::new();
        wrapped.state.nblocks = (1 << 58) + 3;
        let mut plain = Md5Context::new();
        plain.state.nblocks = 3;
        wrapped.update(b"x");
        plain.update(b"x");
        assert_eq!(wrapped.finish(), plain.finish());
    }
}
