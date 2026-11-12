// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES-CTR over messages of any length, from a backend's routine for whole
//! blocks or eight blocks at a time.
//!
//! The counter blocks are `nonce` followed by the big-endian `counter`,
//! `counter + 1`, and so on, wrapping within 32 bits.

/// XORs AES-CTR keystream into `inout` with `apply_8`, which XORs it into
/// eight blocks from the counter given.
///
/// A short final chunk also takes the pipelined eight-block path: the unused
/// blocks cost less than encrypting it one serial block at a time. Counters
/// past the last used block may wrap; they are discarded.
#[cfg(rind_backend = "aarch64")]
pub(crate) fn by8(counter: u32, inout: &mut [u8], mut apply_8: impl FnMut(u32, &mut [u8; 128])) {
    let (chunks, tail) = inout.as_chunks_mut::<128>();
    let mut counter = counter;
    for chunk in chunks {
        apply_8(counter, chunk);
        counter = counter.wrapping_add(8);
    }

    if !tail.is_empty() {
        let mut buf = [0u8; 128];
        buf[..tail.len()].copy_from_slice(tail);
        apply_8(counter, &mut buf);
        tail.copy_from_slice(&buf[..tail.len()]);
    }
}

/// XORs AES-CTR keystream into `inout` with `ctr32`, which XORs it into
/// whole blocks from the counter block given: every whole block in one call,
/// then a final partial block in a copy.
#[cfg(not(rind_backend = "portable"))]
pub(crate) fn blocks(
    nonce: &[u8; 12],
    counter: u32,
    inout: &mut [u8],
    ctr32: impl Fn(&[u8; 16], &mut [[u8; 16]]),
) {
    let (blocks, tail) = inout.as_chunks_mut::<16>();
    let mut ivec = [0u8; 16];
    ivec[..12].copy_from_slice(nonce);
    ivec[12..].copy_from_slice(&counter.to_be_bytes());
    ctr32(&ivec, blocks);

    if !tail.is_empty() {
        let counter = counter.wrapping_add(blocks.len() as u32);
        ivec[12..].copy_from_slice(&counter.to_be_bytes());
        let mut buf = [0u8; 16];
        buf[..tail.len()].copy_from_slice(tail);
        ctr32(&ivec, core::slice::from_mut(&mut buf));
        tail.copy_from_slice(&buf[..tail.len()]);
    }
}
