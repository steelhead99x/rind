// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The two `unsafe` steps the 32-bit portable AES takes, kept apart from its
//! port, whose debug assertions must not sit beside `unsafe`.

/// `v`, which the optimiser can no longer see through, as `md5`'s.
#[inline(always)]
#[cfg(not(any(target_family = "wasm", miri)))]
// The operand appears only in a comment, so no register width is printed.
#[allow(asm_sub_register)]
pub(crate) fn opaque(mut v: u32) -> u32 {
    // SAFETY: the assembly is empty, so it reads, writes, and clobbers
    // nothing but returns `v` in the register it took it in.
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) v, options(pure, nomem, nostack, preserves_flags));
    }
    v
}

// WebAssembly has no stable inline assembly or general-purpose register class,
// and Miri runs none.
#[inline(always)]
#[cfg(any(target_family = "wasm", miri))]
pub(crate) fn opaque(v: u32) -> u32 {
    v
}

/// `bytes` as 32-byte runs of native-endian words and the bytes after them,
/// if `bytes` starts word-aligned, which is public.
#[inline(always)]
pub(crate) fn aligned_pairs(bytes: &mut [u8]) -> Option<(&mut [[u32; 8]], &mut [u8])> {
    if bytes.as_ptr().align_offset(4) != 0 {
        return None;
    }
    let (pairs, rest) = bytes.as_chunks_mut::<32>();
    let n = pairs.len();
    // SAFETY: the start is word-aligned, so each 32-byte run is a `[u32; 8]`
    // in place, and every bit pattern is a valid `u32`.
    let words =
        unsafe { core::slice::from_raw_parts_mut(pairs.as_mut_ptr().cast::<[u32; 8]>(), n) };
    Some((words, rest))
}
