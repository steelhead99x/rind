// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512 compression: pyca/verified-garbage's `vg_sha512_compress_sha512`,
//! imported by `admin/import-vg`, on the SHA-512 instructions, and aws-lc's
//! scalar `sha512-armv8` routine, imported by `admin/import-aws-lc`,
//! otherwise.
//!
//! VG proves its routine in Lean, over its own model of the instructions,
//! which `admin/prove vg` cosimulates, against its contract
//! `compressAArch64`. aws-lc-verification's NSym proof covers the scalar
//! routine as aws-lc builds it for Linux, and `admin/prove-bytes` checks
//! that rind's Linux build matches; that comparison excludes the Apple
//! variant.

use core::mem::MaybeUninit;

use super::cpu::HaveSha3;
use super::vg;

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // The scalar routine runs its loop at least once, so zero blocks would
    // read past `blocks`.
    if blocks.is_empty() {
        return;
    }
    match HaveSha3::check() {
        // SAFETY: `blocks` is a whole number of blocks, and not empty.
        Some(sha3) => unsafe { compress_hw(sha3, state, blocks) },
        // SAFETY: `blocks` is a whole number of blocks, and not empty.
        None => unsafe { compress_nohw(state, blocks) },
    }
}

/// Compresses `blocks`, a whole number of them, into `state` with the
/// SHA-512 instructions.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_hw(_: HaveSha3, state: &mut [u64; 8], blocks: &[u8]) {
    // VG's contract also lends the routine 640 bytes of scratch, which this
    // variant never touches; reserving them costs only stack.
    let mut scratch = MaybeUninit::<[u8; 640]>::uninit();
    // SAFETY: `state` is 64 writable bytes, `blocks` `len / 128` readable
    // blocks, and `scratch` 640 writable bytes. They are distinct objects, so
    // none overlaps another or wraps the address space. The token proves the
    // CPU has the SHA-512 instructions, which Rust's `sha3` feature includes.
    unsafe {
        asm_call!(unsafe extern "C" compress_vg(
            state,
            blocks.as_ptr(),
            blocks.len() / 128,
            scratch.as_mut_ptr().cast::<u8>(),
        ))
    }
}

/// Enters `vg_sha512_compress_sha512` with the arguments its contract,
/// `compressAArch64`, names: `state`, `blocks`, the number of blocks, and
/// `scratch`. VG declares its internal routines without parameters, so Rust
/// may only call it through an entry that declares them; the branch leaves
/// every register, and the return address, as the caller set them.
#[unsafe(naked)]
unsafe extern "C" fn compress_vg(
    _state: *mut [u64; 8],
    _blocks: *const u8,
    _n: usize,
    _scratch: *mut u8,
) {
    core::arch::naked_asm!(
        "b {f}",
        f = sym vg::vg_sha512_compress_sha512::vg_sha512_compress_sha512,
    );
}

/// As [`compress_hw`], with the scalar routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_nohw(state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one.
    unsafe {
        asm_call!(unsafe extern "C" sha512_block_data_order_nohw(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// The round constants, then a zero that ends the scalar routine's rounds.
#[repr(C, align(64))]
struct Table([u64; 81]);

static K512: Table = Table(include!("aws_lc/sha512-armv8.K512.rs"));

#[unsafe(naked)]
unsafe extern "C" fn sha512_block_data_order_nohw(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_nohw.linux.s"),
        K512 = sym K512,
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_nohw.apple.s"),
        K512 = sym K512,
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
        if HaveSha3::check().is_none() {
            return;
        }
        let blocks: Vec<u8> = (0..5 * 128u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for n in 1..=5 {
            let mut want = [
                0x6a09e667f3bcc908,
                0xbb67ae8584caa73b,
                0x3c6ef372fe94f82b,
                0xa54ff53a5f1d36f1,
                0x510e527fade682d1,
                0x9b05688c2b3e6c1f,
                0x1f83d9abfb41bd6b,
                0x5be0cd19137e2179,
            ];
            let mut got = want;
            // SAFETY: `blocks` holds at least `n` blocks, and the CPU has the
            // SHA-512 instructions.
            unsafe {
                asm_call!(unsafe extern "C" sha512_block_data_order_nohw(&mut want, blocks.as_ptr(), n));
                compress_hw(HaveSha3::check().unwrap(), &mut got, &blocks[..128 * n]);
            }
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
