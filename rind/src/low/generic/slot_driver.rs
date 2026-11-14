// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Compiled by `build.rs` on 32-bit portable targets. Not a module of rind.
//!
//! The two exports and the compressors they call land in
//! `.text.rind_rolled_slot`. `build.rs` pads that section to a multiple of
//! 2048 bytes, the set stride of a 16 KiB 8-way cache with 32-byte lines.

#![no_std]

#[allow(dead_code)]
mod sha512 {
    include!("sha512_block.rs");
}

#[allow(dead_code)]
mod sha256 {
    include!("sha256.rs");
}

/// Compresses `len` bytes at `blocks` into the eight-word SHA-512 `state`.
///
/// `len` is a multiple of 128. The bytes and the state are the caller's.
#[unsafe(no_mangle)]
#[unsafe(link_section = ".text.rind_rolled_slot")]
pub unsafe extern "C" fn rind_sha512_compress_blocks(
    state: *mut u64,
    blocks: *const u8,
    len: usize,
) {
    // SAFETY: the rind wrapper passes a live eight-word state and `len`
    // bytes at `blocks`. `len` is a multiple of the block.
    let state = unsafe { &mut *state.cast::<[u64; 8]>() };
    let blocks = unsafe { core::slice::from_raw_parts(blocks, len) };
    sha512::sha512_compress_blocks(state, blocks);
}

/// One padded SHA-256 block for a message of at most 55 bytes.
///
/// `state` is eight chaining words, `message` is `len` bytes, `length` is
/// the 8-byte big-endian bit length, and `out` is 32 bytes.
#[unsafe(no_mangle)]
#[unsafe(link_section = ".text.rind_rolled_slot")]
pub unsafe extern "C" fn rind_sha256_finish_one(
    state: *const u32,
    message: *const u8,
    len: usize,
    length: *const u8,
    out: *mut u8,
) {
    // SAFETY: the rind wrapper passes eight state words, `len` message bytes
    // with `len <= 55` (so the 0x80 and the 8-byte length share this block),
    // eight length bytes, and 32 bytes of output. `len` is the public length.
    let state = unsafe { &*state.cast::<[u32; 8]>() };
    let length = unsafe { &*length.cast::<[u8; 8]>() };
    let mut block = [0u8; 64];
    unsafe {
        core::ptr::copy_nonoverlapping(message, block.as_mut_ptr(), len);
        *block.as_mut_ptr().add(len) = 0x80;
        core::ptr::copy_nonoverlapping(length.as_ptr(), block.as_mut_ptr().add(56), 8);
    }
    let mut h = *state;
    sha256::sha256_compress_block(&mut h, &block);
    unsafe {
        let mut i = 0;
        while i < 8 {
            let bytes = h[i].to_be_bytes();
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), out.add(i * 4), 4);
            i += 1;
        }
    }
}
