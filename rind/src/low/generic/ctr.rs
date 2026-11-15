// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES-CTR over messages of any length, from a backend's routine for whole
//! blocks or eight blocks at a time.
//!
//! The counter blocks are `nonce` followed by the big-endian `counter`,
//! `counter + 1`, and so on, wrapping within 32 bits.

/// A key that XORs counter-mode keystream into eight blocks at a time.
#[cfg(rind_backend = "aarch64")]
pub(crate) trait Ctr8 {
    /// XORs keystream into `chunk`'s eight blocks from the counter blocks
    /// `nonce` followed by the big-endian `counter`, `counter + 1`, and so
    /// on, wrapping within 32 bits.
    fn ctr8(&self, nonce: &[u8; 12], counter: u32, chunk: &mut [u8; 128]);
}

/// XORs AES-CTR keystream into `inout` with `key`, eight blocks at a time.
///
/// A short final chunk also takes the pipelined eight-block path: the unused
/// blocks cost less than encrypting it one serial block at a time. Counters
/// past the last used block may wrap; they are discarded.
///
/// A trait rather than a closure, since Aeneas cannot model a closure that
/// writes through a reference it takes.
#[allow(clippy::needless_range_loop)]
#[cfg(rind_backend = "aarch64")]
pub(crate) fn by8(key: &impl Ctr8, nonce: &[u8; 12], counter: u32, inout: &mut [u8]) {
    let (chunks, tail) = inout.as_chunks_mut::<128>();
    let mut counter = counter;
    // By index: Aeneas translates no loop that writes through an iterator's
    // references.
    for i in 0..chunks.len() {
        key.ctr8(nonce, counter, &mut chunks[i]);
        counter = counter.wrapping_add(8);
    }

    if !tail.is_empty() {
        let mut buf = [0u8; 128];
        buf[..tail.len()].copy_from_slice(tail);
        key.ctr8(nonce, counter, &mut buf);
        tail.copy_from_slice(&buf[..tail.len()]);
    }
}

/// A key that XORs counter-mode keystream into whole blocks.
#[cfg(not(rind_backend = "portable"))]
pub(crate) trait Ctr32 {
    /// XORs keystream into `blocks` from the counter block `ivec`, whose last
    /// four bytes count big-endian, wrapping within 32 bits.
    fn ctr32(&self, ivec: &[u8; 16], blocks: &mut [[u8; 16]]);
}

/// XORs AES-CTR keystream into `inout` with `key`: every whole block in one
/// call, then a final partial block in a copy.
///
/// A trait rather than a closure, since Aeneas cannot model a closure that
/// writes through a reference it takes.
#[cfg(not(rind_backend = "portable"))]
pub(crate) fn blocks(key: &impl Ctr32, nonce: &[u8; 12], counter: u32, inout: &mut [u8]) {
    let (blocks, tail) = inout.as_chunks_mut::<16>();
    let mut ivec = [0u8; 16];
    ivec[..12].copy_from_slice(nonce);
    ivec[12..].copy_from_slice(&counter.to_be_bytes());
    key.ctr32(&ivec, blocks);

    if !tail.is_empty() {
        let counter = counter.wrapping_add(blocks.len() as u32);
        ivec[12..].copy_from_slice(&counter.to_be_bytes());
        let mut buf = [0u8; 16];
        buf[..tail.len()].copy_from_slice(tail);
        key.ctr32(&ivec, core::slice::from_mut(&mut buf));
        tail.copy_from_slice(&buf[..tail.len()]);
    }
}
