// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA2-family hash functions.
//!
//! This is SHA256, SHA384, SHA512, and SHA512/256.
//! These are all described in [FIPS180](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).

use crate::low::{Blockwise, Entry, UpdateBlocks, pad, split_tail};

/// SHA256's chaining value after a whole number of blocks.
///
/// Finishing needs no buffer, so a one-shot hash, or HMAC from its keyed
/// states, works on this alone.
#[derive(Clone)]
pub(crate) struct Sha256State {
    h: [u32; 8],
    // u64 so 32-bit targets can hash past 4 GiB.
    nblocks: u64,
}

impl Sha256State {
    /// SHA256's initial value.
    pub(crate) const fn new() -> Self {
        Self {
            h: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            nblocks: 0,
        }
    }

    fn compress(h: &mut [u32; 8], blocks: &[u8]) {
        Entry::assert_held();
        crate::low::sha256_compress_blocks(h, blocks);
    }

    /// The hash of the input so far followed by `message`, leaving this state as it was.
    pub(crate) fn finish_with(&self, message: &[u8]) -> [u8; Sha256Context::OUTPUT_SZ] {
        let length = self.length(message.len());
        Entry::assert_held();
        crate::low::sha256_finish(&self.h, message, length)
    }

    /// Like [`Self::finish_with`], but stays on the long compressor.
    ///
    /// Used for HMAC's outer hash after a long inner, so a 16 KiB I-cache
    /// keeps HACL*'s SHA-256 body. On backends with no such split this is
    /// `finish_with`.
    pub(crate) fn finish_with_long(&self, message: &[u8]) -> [u8; Sha256Context::OUTPUT_SZ] {
        #[cfg(rind_backend = "portable")]
        {
            let length = self.length(message.len());
            Entry::assert_held();
            crate::low::sha256_finish_long(&self.h, message, length)
        }
        #[cfg(not(rind_backend = "portable"))]
        {
            self.finish_with(message)
        }
    }

    /// Whether [`Self::finish_with`] will use the long compressor for `message`.
    pub(crate) fn finish_uses_long(message: &[u8]) -> bool {
        #[cfg(rind_backend = "portable")]
        {
            crate::low::sha256_finish_uses_long(message)
        }
        #[cfg(not(rind_backend = "portable"))]
        {
            let _ = message;
            false
        }
    }

    /// The padding's length field for the input so far followed by `more` bytes.
    fn length(&self, more: usize) -> [u8; 8] {
        const BLOCK_SZ: usize = Sha256Context::BLOCK_SZ;
        let bits = self
            .nblocks
            .checked_mul(BLOCK_SZ as u64)
            .and_then(|bytes| bytes.checked_add(more as u64))
            .and_then(|bytes| bytes.checked_mul(8))
            .expect("excess data processed by hash function");
        bits.to_be_bytes()
    }
}

impl UpdateBlocks for Sha256State {
    fn update_blocks(&mut self, blocks: &[u8]) {
        debug_assert!(blocks.len().is_multiple_of(Sha256Context::BLOCK_SZ));
        if !blocks.is_empty() {
            // `digest::Context::update` and `hmac::Context::update` leave
            // entering to here.
            let _entry = Entry::new_secret();
            Self::compress(&mut self.h, blocks);
            self.nblocks = self
                .nblocks
                .saturating_add((blocks.len() / Sha256Context::BLOCK_SZ) as u64);
        }
    }
}

/// A context for incremental computation of SHA256.
#[derive(Clone)]
pub(crate) struct Sha256Context {
    state: Sha256State,
    blockwise: Blockwise<{ Self::BLOCK_SZ }>,
}

impl Sha256Context {
    /// Start a new SHA256 hash computation.
    pub(crate) const fn new() -> Self {
        Self::resume(Sha256State::new())
    }

    /// Continue a hash computation from `state`.
    pub(crate) const fn resume(state: Sha256State) -> Self {
        Self {
            state,
            blockwise: Blockwise::new(),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.blockwise.update(bytes, &mut self.state);
    }

    /// Complete the SHA256 computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; Self::OUTPUT_SZ] {
        self.state.finish_with(self.blockwise.buffered())
    }

    /// The internal block size of SHA256.
    pub(crate) const BLOCK_SZ: usize = 64;

    /// The output size of SHA256.
    pub(crate) const OUTPUT_SZ: usize = 32;
}

/// A context for incremental computation of SHA384.
#[derive(Clone)]
pub(crate) struct Sha384Context {
    inner: Sha512Context,
}

impl Sha384Context {
    /// SHA384's initial value.
    pub(crate) const INITIAL: Sha512State = Sha512State::with_h([
        0xcbbb9d5dc1059ed8,
        0x629a292a367cd507,
        0x9159015a3070dd17,
        0x152fecd8f70e5939,
        0x67332667ffc00b31,
        0x8eb44a8768581511,
        0xdb0c2e0d64f98fa7,
        0x47b5481dbefa4fa4,
    ]);

    /// Start a new SHA384 hash computation.
    pub(crate) const fn new() -> Self {
        Self::resume(Self::INITIAL)
    }

    /// Continue a hash computation from `state`.
    pub(crate) const fn resume(state: Sha512State) -> Self {
        Self {
            inner: Sha512Context::resume(state),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.inner.update(bytes)
    }

    /// Complete the SHA384 computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; Self::OUTPUT_SZ] {
        Self::truncate(&self.inner.finish())
    }

    /// The SHA384 output within a SHA512 one.
    pub(crate) fn truncate(output: &[u8; Sha512Context::OUTPUT_SZ]) -> [u8; Self::OUTPUT_SZ] {
        *output.first_chunk().unwrap()
    }

    /// The output size of SHA384.
    pub(crate) const OUTPUT_SZ: usize = 48;
}

/// A context for incremental computation of SHA512/256.
#[derive(Clone)]
pub(crate) struct Sha512_256Context {
    inner: Sha512Context,
}

impl Sha512_256Context {
    /// SHA512/256's initial value.
    pub(crate) const INITIAL: Sha512State = Sha512State::with_h([
        0x22312194fc2bf72c,
        0x9f555fa3c84c64c2,
        0x2393b86b6f53b151,
        0x963877195940eabd,
        0x96283ee2a88effe3,
        0xbe5e1e2553863992,
        0x2b0199fc2c85b8aa,
        0x0eb72ddc81c52ca2,
    ]);

    /// Start a new SHA512/256 hash computation.
    pub(crate) const fn new() -> Self {
        Self {
            inner: Sha512Context::resume(Self::INITIAL),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.inner.update(bytes)
    }

    /// Complete the SHA512/256 computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; Self::OUTPUT_SZ] {
        Self::truncate(&self.inner.finish())
    }

    /// The SHA512/256 output within a SHA512 one.
    pub(crate) fn truncate(output: &[u8; Sha512Context::OUTPUT_SZ]) -> [u8; Self::OUTPUT_SZ] {
        *output.first_chunk().unwrap()
    }

    /// The output size of SHA512/256.
    pub(crate) const OUTPUT_SZ: usize = 32;
}

/// SHA512's chaining value after a whole number of blocks, as [`Sha256State`].
///
/// SHA384 and SHA512/256 share it, from their own initial values.
#[derive(Clone)]
pub(crate) struct Sha512State {
    h: [u64; 8],
    // u64 so 32-bit targets can hash past 4 GiB.
    nblocks: u64,
}

impl Sha512State {
    /// SHA512's initial value.
    pub(crate) const fn new() -> Self {
        Self::with_h([
            0x6a09e667f3bcc908,
            0xbb67ae8584caa73b,
            0x3c6ef372fe94f82b,
            0xa54ff53a5f1d36f1,
            0x510e527fade682d1,
            0x9b05688c2b3e6c1f,
            0x1f83d9abfb41bd6b,
            0x5be0cd19137e2179,
        ])
    }

    /// The truncated variants differ from SHA512 only in this initial value.
    const fn with_h(h: [u64; 8]) -> Self {
        Self { h, nblocks: 0 }
    }

    fn compress(h: &mut [u64; 8], blocks: &[u8]) {
        Entry::assert_held();
        crate::low::sha512_compress_blocks(h, blocks);
    }

    /// The hash of the input so far followed by `message`, leaving this state as it was.
    pub(crate) fn finish_with(&self, message: &[u8]) -> [u8; Sha512Context::OUTPUT_SZ] {
        const BLOCK_SZ: usize = Sha512Context::BLOCK_SZ;
        let bits = (u128::from(self.nblocks) * BLOCK_SZ as u128 + message.len() as u128) * 8;

        // Copies `h` alone: copying the whole state can leave it straddling
        // two stores, which the SHA extensions' 16-byte load of it then
        // waits on instead of forwarding.
        let mut h = self.h;
        let (blocks, rest) = split_tail::<BLOCK_SZ, 16>(message);
        if !blocks.is_empty() {
            Self::compress(&mut h, blocks);
        }
        let mut last = [[0u8; BLOCK_SZ]; 2];
        Self::compress(&mut h, pad(rest, bits.to_be_bytes(), &mut last));

        // Indexes rather than zipping `as_chunks_mut`, which Aeneas cannot
        // translate, so `proofs/` can prove SHA-512.
        let mut r = [0u8; Sha512Context::OUTPUT_SZ];
        for (i, word) in h.iter().enumerate() {
            r[i * 8..(i + 1) * 8].copy_from_slice(&word.to_be_bytes());
        }
        r
    }
}

impl UpdateBlocks for Sha512State {
    fn update_blocks(&mut self, blocks: &[u8]) {
        debug_assert!(blocks.len().is_multiple_of(Sha512Context::BLOCK_SZ));
        if !blocks.is_empty() {
            // `digest::Context::update` and `hmac::Context::update` leave
            // entering to here.
            let _entry = Entry::new_secret();
            Self::compress(&mut self.h, blocks);
            self.nblocks = self
                .nblocks
                .saturating_add((blocks.len() / Sha512Context::BLOCK_SZ) as u64);
        }
    }
}

/// A context for incremental computation of SHA512.
#[derive(Clone)]
pub(crate) struct Sha512Context {
    state: Sha512State,
    blockwise: Blockwise<{ Self::BLOCK_SZ }>,
}

impl Sha512Context {
    /// Start a new SHA512 hash computation.
    pub(crate) const fn new() -> Self {
        Self::resume(Sha512State::new())
    }

    /// Continue a hash computation from `state`.
    pub(crate) const fn resume(state: Sha512State) -> Self {
        Self {
            state,
            blockwise: Blockwise::new(),
        }
    }

    /// Add `bytes` to the ongoing hash computation.
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        self.blockwise.update(bytes, &mut self.state);
    }

    /// Complete the SHA512 computation, returning the hash output.
    pub(crate) fn finish(&self) -> [u8; Self::OUTPUT_SZ] {
        self.state.finish_with(self.blockwise.buffered())
    }

    /// The internal block size of SHA512.
    pub(crate) const BLOCK_SZ: usize = 128;

    /// The output size of SHA512.
    pub(crate) const OUTPUT_SZ: usize = 64;
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn hello() {
        let mut ctx = Sha256Context::new();
        ctx.update(b"hello");
        assert_eq!(&ctx.finish(),
                   b"\x2c\xf2\x4d\xba\x5f\xb0\xa3\x0e\x26\xe8\x3b\x2a\xc5\xb9\xe2\x9e\x1b\x16\x1e\x5c\x1f\xa7\x42\x5e\x73\x04\x33\x62\x93\x8b\x98\x24");

        let mut ctx = Sha512Context::new();
        ctx.update(b"hello");
        assert_eq!(&ctx.finish(),
                   b"\x9b\x71\xd2\x24\xbd\x62\xf3\x78\x5d\x96\xd4\x6a\xd3\xea\x3d\x73\x31\x9b\xfb\xc2\x89\x0c\xaa\xda\xe2\xdf\xf7\x25\x19\x67\x3c\xa7\x23\x23\xc3\xd9\x9b\xa5\xc1\x1d\x7c\x7a\xcc\x6e\x14\xb8\xc5\xda\x0c\x46\x63\x47\x5c\x2e\x5c\x3a\xde\xf4\x6f\x73\xbc\xde\xc0\x43");
    }

    // The bit length overflows a 32-bit usize at 512 MiB, and the byte count
    // at 4 GiB.
    #[test]
    fn length_past_32_bit_usize() {
        for bytes in [1u64 << 29, 1 << 32] {
            let mut ctx = Sha256Context::new();
            ctx.state.nblocks = bytes / Sha256Context::BLOCK_SZ as u64;
            ctx.update(b"x");
            ctx.finish();

            let mut ctx = Sha512Context::new();
            ctx.state.nblocks = bytes / Sha512Context::BLOCK_SZ as u64;
            ctx.update(b"x");
            ctx.finish();
        }
    }

    #[test]
    fn sha512_long() {
        let mut data = Vec::with_capacity(1024);
        for i in 0..1024 {
            data.push(i as u8);
        }
        let mut ctx = Sha512Context::new();
        ctx.update(&data);
        assert_eq!(
            &ctx.finish(),
            &[
                55, 246, 82, 190, 134, 127, 40, 237, 3, 50, 105, 203, 186, 32, 26, 242, 17, 44, 43,
                63, 211, 52, 168, 159, 210, 247, 87, 147, 141, 222, 232, 21, 120, 124, 198, 29,
                110, 36, 168, 163, 51, 64, 208, 247, 232, 111, 252, 5, 136, 22, 184, 133, 48, 118,
                107, 166, 226, 49, 98, 10, 19, 11, 86, 108
            ]
        );
    }

    #[test]
    fn sha256_all_lengths() {
        // see cifra `vector_length` and associated
        let mut outer = Sha256Context::new();

        for len in 0..1024 {
            let mut inner = Sha256Context::new();

            for _ in 0..len {
                inner.update(&[len as u8]);
            }

            outer.update(&inner.finish());
        }

        assert_eq!(&outer.finish(),
                   b"\x55\x7b\xfd\xd5\xef\xda\xfd\x63\x06\x5e\xb7\x98\x87\xde\x86\xdb\x54\xc3\xfe\xdf\x7b\xcc\xcb\x97\x08\xfa\x87\xf0\x11\x87\x61\xdc");
    }
    #[test]
    fn sha256_finish_long_matches_finish_with() {
        // The long path is only a compressor choice; every length must
        // match the ordinary finish, including HMAC's 32-byte outer hash.
        let prefix = [0x5au8; 128];
        let mut state = Sha256State::new();
        state.update_blocks(&prefix);
        for len in 0..=400 {
            let message: Vec<u8> = (0..len).map(|i| i as u8).collect();
            assert_eq!(
                state.finish_with(&message),
                state.finish_with_long(&message),
                "{len} bytes after 128-byte prefix"
            );
            let fresh = Sha256State::new();
            assert_eq!(
                fresh.finish_with(&message),
                fresh.finish_with_long(&message),
                "{len} bytes from the initial state"
            );
        }
        // `split_tail` holds the last block when the padding fits after it.
        // A 320-byte message therefore has a 256-byte prefix, which is the
        // cutover and still rolled; 376 bytes leaves a 56-byte tail that
        // does not fit the padding, so its 320-byte prefix is long, and so
        // is a 384-byte message.
        let prefix = |n: usize| split_tail::<64, 8>(&vec![0u8; n]).0.len();
        assert_eq!(prefix(256), 192);
        assert_eq!(prefix(320), 256);
        assert_eq!(prefix(375), 256);
        assert_eq!(prefix(376), 320);
        assert_eq!(prefix(384), 320);
        #[cfg(all(rind_backend = "portable", target_pointer_width = "32"))]
        {
            assert!(!Sha256State::finish_uses_long(&[0u8; 320]));
            assert!(!Sha256State::finish_uses_long(&[0u8; 375]));
            assert!(Sha256State::finish_uses_long(&[0u8; 376]));
            assert!(Sha256State::finish_uses_long(&[0u8; 384]));
            assert!(!Sha256State::finish_uses_long(&[0u8; 256]));
            assert!(!Sha256State::finish_uses_long(&[0u8; 32]));
        }
        #[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
        {
            assert!(!Sha256State::finish_uses_long(&[0u8; 384]));
        }
    }

    #[test]
    fn sha512_all_lengths() {
        let mut outer = Sha512Context::new();

        for len in 0..1024 {
            let mut inner = Sha512Context::new();

            for _ in 0..len {
                inner.update(&[len as u8]);
            }

            outer.update(&inner.finish());
        }

        assert_eq!(&outer.finish(),
                   b"\x61\x20\x81\x2e\xd5\x0c\xc3\x11\x67\x04\x3f\x1f\x06\x9d\xcd\x4a\xd8\x83\x23\xd9\x96\x53\xd9\x67\x38\x2c\xc3\x44\x25\x69\x53\x1c\xd0\x3d\xe4\x79\x0a\x71\xde\x88\x45\x44\x66\x80\xb8\xc5\x90\xb3\x07\xc8\xae\x52\x57\x67\xf9\x28\xf8\xda\x9e\x9e\x80\xc9\x35\x5e");
    }
}
