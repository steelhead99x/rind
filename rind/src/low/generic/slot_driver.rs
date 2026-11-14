// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Compiled by `build.rs` for the native slot and directly in host tests.
//!
//! The two exports and the compressors they call land in
//! `.text.rind_rolled_slot`. `build.rs` pads the slot plus measured slack to
//! a multiple of 2048 bytes, the set stride of a 16 KiB 8-way cache.

#![cfg_attr(sha_slot_driver, no_std)]

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
#[cfg_attr(sha_slot_driver, unsafe(export_name = concat!(env!("RIND_SLOT_PREFIX"), "_sha512_compress_blocks")))]
#[cfg_attr(sha_slot_driver, unsafe(link_section = ".text.rind_rolled_slot"))]
pub(crate) unsafe extern "C" fn rind_sha512_compress_blocks(
    state: *mut u64,
    blocks: *const u8,
    len: usize,
) {
    // SAFETY: the rind wrapper passes a live eight-word state and `len`
    // bytes at `blocks`. `len` is a multiple of the block.
    let state = unsafe { &mut *state.cast::<[u64; 8]>() };
    // SAFETY: the caller supplies the stated number of live block bytes.
    let blocks = unsafe { core::slice::from_raw_parts(blocks, len) };
    sha512::sha512_compress_blocks(state, blocks);
}

/// One padded SHA-256 block for a message of at most 55 bytes.
///
/// `state` is eight chaining words, `message` is `len` bytes, `length` is
/// the 8-byte big-endian bit length, and `out` is 32 bytes.
#[cfg_attr(sha_slot_driver, unsafe(export_name = concat!(env!("RIND_SLOT_PREFIX"), "_sha256_finish_one")))]
#[cfg_attr(sha_slot_driver, unsafe(link_section = ".text.rind_rolled_slot"))]
pub(crate) unsafe extern "C" fn rind_sha256_finish_one(
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
    // SAFETY: the caller supplies eight live length bytes.
    let length = unsafe { &*length.cast::<[u8; 8]>() };
    let mut block = [0u8; 64];
    // SAFETY: len is at most 55, so both inputs and padding fit this block.
    unsafe {
        core::ptr::copy_nonoverlapping(message, block.as_mut_ptr(), len);
        *block.as_mut_ptr().add(len) = 0x80;
        core::ptr::copy_nonoverlapping(length.as_ptr(), block.as_mut_ptr().add(56), 8);
    }
    let mut h = *state;
    sha256::sha256_compress_block(&mut h, &block);
    // SAFETY: the caller supplies 32 writable output bytes, disjoint from h.
    unsafe {
        let mut i = 0;
        while i < 8 {
            let bytes = h[i].to_be_bytes();
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), out.add(i * 4), 4);
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slot_sha256_matches_backend() {
        for len in 0..=55 {
            let message: Vec<u8> = (0..len).map(|i| (i * 17 + 3) as u8).collect();
            // A non-IV chaining value also exercises resumed HMAC state.
            let state = [0x9e37_79b9u32; 8];
            let length = ((len as u64 + 64) * 8).to_be_bytes();
            let mut padded = [0u8; 64];
            padded[..len].copy_from_slice(&message);
            padded[len] = 0x80;
            padded[56..].copy_from_slice(&length);
            let mut expected = state;
            crate::low::sha256_compress_blocks(&mut expected, &padded);
            let expected = crate::low::sha256_digest(&expected);
            crate::low::ct::secret_slice(&state);
            crate::low::ct::secret_slice(&message);
            let mut got = [0; 32];
            // SAFETY: every pointer has the size required by the slot, and
            // `len <= 55` leaves room for this one block's padding.
            unsafe {
                rind_sha256_finish_one(
                    state.as_ptr(),
                    message.as_ptr(),
                    len,
                    length.as_ptr(),
                    got.as_mut_ptr(),
                );
            }
            assert_eq!(crate::low::ct::into_public(got), expected, "{len}");
        }
    }

    #[test]
    fn slot_sha512_matches_backend() {
        for len in [0, 128, 256, 1024] {
            let blocks: Vec<u8> = (0..len).map(|i| (i * 17 + 3) as u8).collect();
            let mut state = [0x9e37_79b9_1234_5678u64; 8];
            let mut expected = state;
            crate::low::sha512_compress_blocks(&mut expected, &blocks);
            crate::low::ct::secret_slice(&state);
            crate::low::ct::secret_slice(&blocks);
            // SAFETY: the eight-word state and whole blocks are live.
            unsafe {
                rind_sha512_compress_blocks(state.as_mut_ptr(), blocks.as_ptr(), len);
            }
            assert_eq!(crate::low::ct::into_public(state), expected, "{len}");
        }
    }
}
