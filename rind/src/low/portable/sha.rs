// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 on rind's portable code in `generic`, as armv7 runs it without the
//! crypto extension, and the SHA-2 family on HACL*'s verified
//! `Hacl_Hash_SHA2`, as libcrux-sha2 ships it. HACL*'s SHA-256 took 0.67-0.93
//! of `generic`'s time at 16 KB on x86_64.

use libcrux_sha2::hacl::sha256_update_nblocks;
#[cfg(target_pointer_width = "64")]
use libcrux_sha2::hacl::sha512_update_nblocks;

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;

/// HACL* takes a 32-bit length, so longer input goes in pieces of whole
/// blocks below it.
const PIECE: usize = 1 << 31;

/// Compresses whole 64-byte `blocks` into `state`.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    for piece in blocks.chunks(PIECE) {
        sha256_update_nblocks(piece.len() as u32, piece, state);
    }
}

/// Compresses `message`, padded and closed by the big-endian bit `length`.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha1_compress_blocks(state, blocks);
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha256_compress_blocks(&mut h, blocks);
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(&mut h, crate::low::pad(rest, length, &mut last));
    crate::low::sha256_digest(&h)
}

/// Compresses whole 128-byte `blocks` into `state`.
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // HACL*'s `sha512_update` is fully unrolled (~47 KiB on Xtensa), which
    // is several times a 16 KiB instruction cache. On 32-bit targets use
    // the rolled compression in `generic::sha512` instead. 64-bit portable
    // keeps HACL*, which is faster when the code stays cached.
    #[cfg(target_pointer_width = "32")]
    {
        crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
    }
    #[cfg(target_pointer_width = "64")]
    {
        for piece in blocks.chunks(PIECE) {
            sha512_update_nblocks(piece.len() as u32, piece, state);
        }
    }
}
