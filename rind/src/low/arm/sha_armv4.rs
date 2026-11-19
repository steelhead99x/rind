// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1, SHA-256, and SHA-512 on armv7. SHA-1 runs aws-lc's `sha1-armv4-large`
//! routines: the AArch32 crypto extension's where the CPU has it, else NEON
//! where it has that, and integer code otherwise. SHA-256 runs aws-lc's
//! `sha256-armv4` crypto-extension routine where the CPU has it, and
//! `generic::sha256` otherwise, and SHA-512 always runs `generic::sha512`.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. It is not
//! formally verified: its correctness rests on its use and testing in OpenSSL,
//! BoringSSL, and aws-lc, and on rind's tests of it against the portable code,
//! CAVP, and aws-lc-rs.
//!
//! The portable bodies replace aws-lc's integer and NEON SHA-256 and SHA-512:
//! 32-bit Arm NEON and SHA intrinsics are unstable on the toolchain this crate
//! builds with (`stdarch_arm_neon_intrinsics`), and stable Rust has no way to
//! emit `sha256h`, so the crypto extension's instructions stay assembly. On a
//! Cortex-A7, SHA-1 in Rust took 1.88 times aws-lc's assembly, so it stays.

use super::cpu::{HaveCryptoExt, HaveNeon};
use crate::low::{pad, sha256_digest, split_tail};

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("sha1_block_data_order_nohw")]
    fn sha1_block_data_order_nohw(state: *mut [u32; 5], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha1_block_data_order_neon")]
    fn sha1_block_data_order_neon(state: *mut [u32; 5], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha1_block_data_order_hw")]
    fn sha1_block_data_order_hw(state: *mut [u32; 5], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha256_block_data_order_hw")]
    fn sha256_block_data_order_hw(state: *mut [u32; 8], data: *const u8, blocks: usize);
}

// As in `aesv8_armx`: ARM mode with NEON, then the target's `.fpu` again.
core::arch::global_asm!(
    ".text",
    ".fpu neon",
    ".code 32",
    include_str!("aws_lc/sha1-armv4-large.s"),
    include_str!("aws_lc/sha256-armv4.s"),
    ".fpu vfpv3",
    sha1_block_data_order_nohw = sym sha1_block_data_order_nohw,
    sha1_block_data_order_neon = sym sha1_block_data_order_neon,
    sha1_block_data_order_hw = sym sha1_block_data_order_hw,
    sha256_block_data_order_hw = sym sha256_block_data_order_hw,
);

pub(crate) fn sha1_compress_blocks(state: &mut [u32; 5], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    // Every routine runs its loop at least once, so zero blocks would read
    // past `blocks`.
    if blocks.is_empty() {
        return;
    }
    let (data, num) = (blocks.as_ptr(), blocks.len() / 64);
    if HaveCryptoExt::check().is_some() {
        // SAFETY: `blocks` is `num` readable blocks, and the token proves the
        // CPU has the SHA-1 instructions.
        unsafe { asm_call!(unsafe extern "C" sha1_block_data_order_hw(state, data, num)) }
    } else if HaveNeon::check().is_some() {
        // SAFETY: `blocks` is `num` readable blocks, and the token proves the
        // CPU has NEON.
        unsafe { asm_call!(unsafe extern "C" sha1_block_data_order_neon(state, data, num)) }
    } else {
        // SAFETY: `blocks` is `num` readable blocks.
        unsafe { asm_call!(unsafe extern "C" sha1_block_data_order_nohw(state, data, num)) }
    }
}

/// Compresses the end of `message`, padded and closed by `length`.
// Out of line, so `Sha1State::finish_with` stays small enough to inline and
// write the digest where its caller keeps it.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = split_tail::<64, 8>(message);
    if !blocks.is_empty() {
        sha1_compress_blocks(state, blocks);
    }
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, pad(rest, length, &mut last));
}

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    // The routine runs its loop at least once, so zero blocks would read past
    // `blocks`.
    if blocks.is_empty() {
        return;
    }
    if HaveCryptoExt::check().is_some() {
        // SAFETY: `blocks` is `blocks.len() / 64` readable blocks, at least
        // one, and the token proves the CPU has the SHA-256 instructions.
        unsafe {
            asm_call!(unsafe extern "C" sha256_block_data_order_hw(state, blocks.as_ptr(), blocks.len() / 64))
        }
    } else {
        crate::low::generic::sha256::sha256_compress_blocks(state, blocks);
    }
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
