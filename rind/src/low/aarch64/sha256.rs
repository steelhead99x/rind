// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 compression with aws-lc's `sha256-armv8` routines, imported by
//! `admin/import-aws-lc`: the SHA-256 instructions where the CPU has them,
//! and scalar code otherwise.
//!
//! rind's Lean proof, `proofs/Rind/Aarch64/Sha256HwAsm.lean`, covers the
//! routine for the SHA-256 instructions as rind's Linux build emits it, its
//! leakage contract included; Apple's build assembles its own copy.
//! The scalar routine is not formally verified: its correctness rests on its
//! use and testing in OpenSSL, BoringSSL, and aws-lc, and on rind's tests of
//! it against the other, CAVP, and aws-lc-rs.

use super::cpu::HaveCryptoExt;

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    // Both routines run their loop at least once, so zero blocks would read
    // past `blocks`.
    if blocks.is_empty() {
        return;
    }
    match HaveCryptoExt::check() {
        // SAFETY: `blocks` is a whole number of blocks, and not empty.
        Some(crypto) => unsafe { compress_hw(crypto, state, blocks) },
        // SAFETY: `blocks` is a whole number of blocks, and not empty.
        None => unsafe { compress_nohw(state, blocks) },
    }
}

/// Compresses `blocks`, a whole number of them, into `state` with the
/// SHA-256 instructions.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_hw(_: HaveCryptoExt, state: &mut [u32; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 64` readable blocks, at least one, and the
    // token proves the CPU has the SHA-256 instructions.
    unsafe {
        asm_call!(unsafe extern "C" sha256_block_data_order_hw(state, blocks.as_ptr(), blocks.len() / 64))
    }
}

/// As [`compress_hw`], with the scalar routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_nohw(state: &mut [u32; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 64` readable blocks, at least one.
    unsafe {
        asm_call!(unsafe extern "C" sha256_block_data_order_nohw(state, blocks.as_ptr(), blocks.len() / 64))
    }
}

/// Compresses the end of `message`, padded and closed by `length`.
// Out of line, as `sha1_compress_padded` is, so `finish_with` inlines.
#[inline(never)]
fn sha256_compress_padded(state: &mut [u32; 8], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    if !blocks.is_empty() {
        sha256_compress_blocks(state, blocks);
    }
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    sha256_compress_padded(&mut h, message, length);
    crate::low::sha256_digest(&h)
}

/// The round constants, then a zero that ends the scalar routine's rounds.
#[repr(C, align(64))]
struct Table([u32; 65]);

static K256: Table = Table(include!("aws_lc/sha256-armv8.K256.rs"));

#[unsafe(naked)]
unsafe extern "C" fn sha256_block_data_order_nohw(
    state: *mut [u32; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_nohw.linux.s"),
        K256 = sym K256,
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_nohw.apple.s"),
        K256 = sym K256,
    );
}

#[unsafe(naked)]
unsafe extern "C" fn sha256_block_data_order_hw(
    state: *mut [u32; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_hw.linux.s"),
        K256 = sym K256,
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_hw.apple.s"),
        K256 = sym K256,
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Every other test sees only the routine the CPU picks, so the two are
    // checked against each other here: odd and even block counts, with
    // distinct bytes in every block.
    #[test]
    fn hw_matches_nohw() {
        if HaveCryptoExt::check().is_none() {
            return;
        }
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for n in 1..=5 {
            let mut want = [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ];
            let mut got = want;
            // SAFETY: `blocks` holds at least `n` blocks, and the CPU has the
            // SHA-256 instructions.
            unsafe {
                asm_call!(unsafe extern "C" sha256_block_data_order_nohw(&mut want, blocks.as_ptr(), n));
                asm_call!(unsafe extern "C" sha256_block_data_order_hw(&mut got, blocks.as_ptr(), n));
            }
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
