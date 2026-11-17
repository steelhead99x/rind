// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1, SHA-256, and SHA-512 on armv7, on the portable bodies in `generic`.
//!
//! 32-bit Arm NEON and SHA intrinsics are unstable on the toolchain this
//! crate builds with (`stdarch_arm_neon_intrinsics`), so this backend does
//! not ship a second compressor.

use crate::low::{pad, sha256_digest, split_tail};

pub(crate) fn sha1_compress_blocks(state: &mut [u32; 5], blocks: &[u8]) {
    crate::low::generic::sha1::sha1_compress_blocks(state, blocks);
}

/// Compresses the end of `message`, padded and closed by `length`.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = split_tail::<64, 8>(message);
    sha1_compress_blocks(state, blocks);
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, pad(rest, length, &mut last));
}

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    crate::low::generic::sha256::sha256_compress_blocks(state, blocks);
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = split_tail::<64, 8>(message);
    sha256_compress_blocks(&mut h, blocks);
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(&mut h, pad(rest, length, &mut last));
    sha256_digest(&h)
}

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
}
