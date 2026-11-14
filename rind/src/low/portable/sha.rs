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
/// A context finish compares already-compressed bytes with this too.
#[cfg(target_pointer_width = "32")]
pub(crate) const SHA256_SHORT: usize = 256;

/// Compresses whole 64-byte `blocks` into `state`.
///
/// 64-bit portable is main's body: the HACL* loop, inlined. On 32-bit this
/// is the per-call cutover for callers that have no running byte count
/// (`guard_pages`, tests). `digest::Context::update` does not use it. A long
/// one-shot calls [`sha256_hacl_nblocks`] from its own `Blockwise`
/// monomorphization, which has no relocation to the rolled compressor, and a
/// short flush calls [`sha256_compress_rolled`] with the same separation.
/// Keeping both symbols in this function is what put the rolled loop on the
/// long update's path.
// 32-bit production code calls `sha256_hacl_nblocks` or
// `sha256_compress_rolled` directly. This hybrid remains for tests, which
// pass every length through one function.
#[cfg(any(target_pointer_width = "64", test))]
#[cfg_attr(target_pointer_width = "32", inline(never))]
#[cfg_attr(target_pointer_width = "64", inline)]
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    #[cfg(target_pointer_width = "32")]
    {
        if blocks.len() <= SHA256_SHORT {
            sha256_compress_rolled(state, blocks);
        } else {
            sha256_hacl_nblocks(state, blocks);
        }
    }
    #[cfg(target_pointer_width = "64")]
    {
        sha256_hacl_nblocks(state, blocks);
    }
}

/// HACL*'s `sha256_update_nblocks` loop, the whole of main's
/// `sha256_compress_blocks`.
///
/// One out-of-line copy on 32-bit, shared by a long `Context::update` and by
/// `sha256_finish_long`. The rolled compressor is not named here. Inlining
/// this into both callers would emit two copies of the ~12 KiB body, and a
/// 16 KiB I-cache cannot hold both across update and finish.
#[cfg_attr(target_pointer_width = "32", inline(never))]
#[cfg_attr(target_pointer_width = "64", inline)]
pub(crate) fn sha256_hacl_nblocks(state: &mut [u32; 8], blocks: &[u8]) {
    for piece in blocks.chunks(PIECE) {
        sha256_update_nblocks(piece.len() as u32, piece, state);
    }
}

/// The rolled compressor, out of line so a long update or a long finish does
/// not name it. Short HMAC pads and a hash still inside [`SHA256_SHORT`]
/// bytes of bulk are the callers. No HACL* symbol.
#[cfg(target_pointer_width = "32")]
#[inline(never)]
pub(crate) fn sha256_compress_rolled(state: &mut [u32; 8], blocks: &[u8]) {
    crate::low::generic::sha256::sha256_compress_blocks(state, blocks);
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
/// to use HACL*, the padding stays on HACL* too. Switching to the rolled
/// loop after HACL*'s ~12 KiB body evicts that body from a 16 KiB 8-way
/// I-cache when the two functions land in the same sets, and the next call
/// refills the body from flash.
#[cfg(target_pointer_width = "32")]
#[inline(always)]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    sha256_finish_body::<false>(state, message, length)
}

/// 64-bit portable always finishes on HACL*.
#[cfg(target_pointer_width = "64")]
#[inline(always)]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    sha256_finish_hacl(state, message, length)
}

/// Like [`sha256_finish`], but uses HACL* even for a short `message`.
///
/// HMAC's outer hash is 32 bytes. After a long inner hash already brought
/// HACL* into a 16 KiB I-cache, staying on it avoids evicting that body
/// with the rolled loop before the next tag. The 32-bit body is its own
/// monomorphization, so the rolled loop is not in the function a long
/// finish runs.
#[cfg(target_pointer_width = "32")]
#[inline(always)]
pub(crate) fn sha256_finish_long(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    sha256_finish_body::<true>(state, message, length)
}

/// 64-bit portable has no rolled SHA-256, so this is [`sha256_finish`].
#[cfg(target_pointer_width = "64")]
#[inline(always)]
pub(crate) fn sha256_finish_long(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    sha256_finish_hacl(state, message, length)
}

/// Whether [`sha256_finish`] will use HACL* for `message` on this target.
#[inline]
pub(crate) fn sha256_finish_uses_long(message: &[u8]) -> bool {
    #[cfg(target_pointer_width = "32")]
    {
        let (blocks, _) = crate::low::split_tail::<64, 8>(message);
        blocks.len() > SHA256_SHORT
    }
    #[cfg(target_pointer_width = "64")]
    {
        let _ = message;
        false
    }
}

/// `FORCE_LONG` is a monomorphization, not a runtime flag, so the long
/// copy does not contain the rolled compressor.
#[cfg(target_pointer_width = "32")]
#[inline(always)]
fn sha256_finish_body<const FORCE_LONG: bool>(
    state: &[u32; 8],
    message: &[u8],
    length: [u8; 8],
) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    let mut last = [[0u8; 64]; 2];
    let padded = crate::low::pad(rest, length, &mut last);
    if !FORCE_LONG && blocks.len() <= SHA256_SHORT {
        sha256_compress_rolled(&mut h, blocks);
        sha256_compress_rolled(&mut h, padded);
    } else {
        sha256_hacl_nblocks(&mut h, blocks);
        sha256_hacl_nblocks(&mut h, padded);
    }
    crate::low::sha256_digest(&h)
}

#[cfg(target_pointer_width = "64")]
#[inline(never)]
fn sha256_finish_hacl(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    let mut last = [[0u8; 64]; 2];
    let padded = crate::low::pad(rest, length, &mut last);
    sha256_hacl_nblocks(&mut h, blocks);
    sha256_hacl_nblocks(&mut h, padded);
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
