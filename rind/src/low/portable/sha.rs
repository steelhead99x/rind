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

/// Byte length at or below which 32-bit portable SHA-256 uses the rolled
/// compressor. Shared by `sha256_compress_blocks` and `sha256_finish`.
#[cfg(target_pointer_width = "32")]
const SHORT: usize = 256;

/// Compresses whole 64-byte `blocks` into `state`.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    // HACL*'s `sha256_update` is fully unrolled (~12 KiB on Xtensa), which
    // fills a 16 KiB instruction cache and makes short inputs and HMAC/HKDF
    // pay a large miss cost. On 32-bit targets, short calls (HMAC pads,
    // HKDF, 32-64 byte hashes) use the rolled `generic::sha256`; longer
    // calls use HACL*, which is faster once that 12 KiB stays hot.
    // Cutover is 256 bytes (4 blocks): on the ESP32-S3, rolled was 0.77×
    // at 32 B and 0.99× at 64 B, and HACL* was 0.78× rolled at 1200 B
    // and 0.68× at 16 KB. 64-bit portable always keeps HACL*.
    #[cfg(target_pointer_width = "32")]
    {
        if blocks.len() <= SHORT {
            crate::low::generic::sha256::sha256_compress_blocks(state, blocks);
        } else {
            sha256_hacl_nblocks(state, blocks);
        }
    }
    #[cfg(target_pointer_width = "64")]
    {
        sha256_hacl_nblocks(state, blocks);
    }
}

fn sha256_hacl_nblocks(state: &mut [u32; 8], blocks: &[u8]) {
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
///
/// On 32-bit targets, once the whole-block part of `message` is long enough
/// to use HACL*, the padding stays on HACL* too. Switching to the 477-byte
/// rolled loop after HACL*'s 12 KiB body evicts that body from a 16 KiB
/// 8-way I-cache when the two functions' offsets in a 16 KiB page overlap,
/// and the next call then refills 12 KiB from flash. HMAC's reused-key
/// path (two `finish_with` calls per tag) is what showed this on the
/// ESP32-S3: 13–14% slower at 1200–1350 B after a layout shift, with
/// identical machine code.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    sha256_finish_on(state, message, length, false)
}

/// Like [`sha256_finish`], but uses HACL* even for a short `message`.
///
/// HMAC's outer hash is 32 bytes. After a long inner hash already brought
/// HACL* into a 16 KiB I-cache, staying on it avoids evicting that body
/// with the rolled loop before the next tag.
#[inline]
pub(crate) fn sha256_finish_long(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    sha256_finish_on(state, message, length, true)
}

/// Whether [`sha256_finish`] will use HACL* for `message` on this target.
pub(crate) fn sha256_finish_uses_long(message: &[u8]) -> bool {
    #[cfg(target_pointer_width = "32")]
    {
        let (blocks, _) = crate::low::split_tail::<64, 8>(message);
        blocks.len() > SHORT
    }
    #[cfg(target_pointer_width = "64")]
    {
        let _ = message;
        false
    }
}

fn sha256_finish_on(
    state: &[u32; 8],
    message: &[u8],
    length: [u8; 8],
    force_long: bool,
) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    let mut last = [[0u8; 64]; 2];
    let padded = crate::low::pad(rest, length, &mut last);

    #[cfg(target_pointer_width = "32")]
    {
        if !force_long && blocks.len() <= SHORT {
            crate::low::generic::sha256::sha256_compress_blocks(&mut h, blocks);
            crate::low::generic::sha256::sha256_compress_blocks(&mut h, padded);
        } else {
            sha256_hacl_nblocks(&mut h, blocks);
            sha256_hacl_nblocks(&mut h, padded);
        }
    }
    #[cfg(target_pointer_width = "64")]
    {
        let _ = force_long;
        sha256_hacl_nblocks(&mut h, blocks);
        sha256_hacl_nblocks(&mut h, padded);
    }
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
