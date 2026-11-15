// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512 compression: OpenSSL's `sha512-x86_64` routines for the SHA512
//! instructions and for AVX2, imported by `admin/import-openssl`, and
//! aws-lc's AVX and scalar ones, imported by `admin/import-aws-lc`.
//!
//! aws-lc-verification's SAW proof covers aws-lc's AVX routine, as aws-lc
//! builds it, and rind's HOL Light proof in `proofs/hol-light/` covers
//! OpenSSL's AVX2 routine, as rind builds it; nothing verifies the others.

use std::sync::OnceLock;

use super::cpu::{HaveAvx, HaveAvx2, HaveSha512, is_intel};

/// The SHA-512 routine this CPU runs, with the proof it may.
#[derive(Clone, Copy)]
enum Path {
    Sha512ext(HaveSha512),
    Avx2(HaveAvx2),
    Avx(HaveAvx),
    Nohw,
}

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // The routines other than the SHA512 instructions' run their loop at
    // least once, so zero blocks would read past `blocks`.
    if blocks.is_empty() {
        return;
    }
    match path() {
        // SAFETY: `blocks` is a whole number of blocks, and not empty.
        Path::Sha512ext(token) => unsafe { compress_sha512ext(token, state, blocks) },
        // SAFETY: as above.
        Path::Avx2(token) => unsafe { compress_avx2(token, state, blocks) },
        // SAFETY: as above.
        Path::Avx(token) => unsafe { compress_avx(token, state, blocks) },
        // SAFETY: as above.
        Path::Nohw => unsafe { compress_nohw(state, blocks) },
    }
}

fn path() -> Path {
    // Picked once, rather than testing several features on every compression.
    static PATH: OnceLock<Path> = OnceLock::new();
    *PATH.get_or_init(pick)
}

fn pick() -> Path {
    if let Some(token) = HaveSha512::check() {
        Path::Sha512ext(token)
    } else if let Some(token) = HaveAvx2::check() {
        Path::Avx2(token)
    } else if let Some(token) = HaveAvx::check().filter(|_| is_intel()) {
        // The AVX routine is the faster on Intel's cores and the slower on
        // AMD's, so rind picks by vendor as aws-lc does.
        Path::Avx(token)
    } else {
        Path::Nohw
    }
}

/// Compresses `blocks`, a whole number of them, into `state` with the
/// routine for the SHA512 instructions.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_sha512ext(_: HaveSha512, state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, and the token proves
    // the SHA512 instructions and AVX2.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_sha512ext(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// As [`compress_sha512ext`], with the AVX2 routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_avx2(_: HaveAvx2, state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one, and the
    // token proves AVX2, BMI1, and BMI2.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_avx2(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// As [`compress_sha512ext`], with the AVX routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_avx(_: HaveAvx, state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one, and the
    // token proves AVX.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_avx(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// As [`compress_sha512ext`], with the scalar routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_nohw(state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_nohw(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// The round constants, each pair twice for the vector additions, then the
/// byte-swap mask, as the routines other than the SHA512 instructions' load
/// them; that one loads only the mask from here.
#[repr(C, align(64))]
struct Table([u64; 164]);

static K512: Table = Table(include!("aws_lc/sha512-x86_64.K512.rs"));

/// The round constants once each, as the SHA512 instructions' routine loads
/// them.
#[repr(C, align(64))]
struct SingleTable([u64; 80]);

static K512_SINGLE: SingleTable = SingleTable(include!("openssl/sha512-x86_64.K512_single.rs"));

// The routines take the System V ABI on every OS, since their text is
// OpenSSL's and aws-lc's ELF and Mach-O flavors, which read their arguments
// from its registers.

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_sha512ext(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/sha512_block_data_order_sha512ext.linux.s"),
        K512 = sym K512,
        K512_single = sym K512_SINGLE,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/sha512_block_data_order_sha512ext.apple.s"),
        K512 = sym K512,
        K512_single = sym K512_SINGLE,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_avx2(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/sha512_block_data_order_avx2.linux.s"),
        K512 = sym K512,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/sha512_block_data_order_avx2.apple.s"),
        K512 = sym K512,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_avx(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_avx.linux.s"),
        K512 = sym K512,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_avx.apple.s"),
        K512 = sym K512,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_nohw(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_nohw.linux.s"),
        K512 = sym K512,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_nohw.apple.s"),
        K512 = sym K512,
        options(att_syntax),
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;

    // Every other test sees only the routine this CPU picks, so each the CPU
    // can run is checked against the scalar one here, on blocks
    // `admin/ctgrind` keeps secret: odd and even block counts, with distinct
    // bytes in every block. That checks Intel's AVX code, which only Intel
    // CPUs without AVX2 pick, on any CPU.
    #[test]
    fn paths_match_nohw() {
        let blocks: Vec<u8> = (0..5 * 128u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        ct::secret_slice(&blocks);
        for n in 1..=5 {
            let blocks = &blocks[..n * 128];
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
            let start = want;
            // SAFETY: `blocks` holds `n` blocks, at least one.
            unsafe { compress_nohw(&mut want, blocks) };
            let want = ct::into_public(want);
            if let Some(token) = HaveAvx::check() {
                let mut got = start;
                // SAFETY: as above.
                unsafe { compress_avx(token, &mut got, blocks) };
                assert_eq!(ct::into_public(got), want, "avx, {n} blocks");
            }
            if let Some(token) = HaveAvx2::check() {
                let mut got = start;
                // SAFETY: as above.
                unsafe { compress_avx2(token, &mut got, blocks) };
                assert_eq!(ct::into_public(got), want, "avx2, {n} blocks");
            }
            if let Some(token) = HaveSha512::check() {
                let mut got = start;
                // SAFETY: as above.
                unsafe { compress_sha512ext(token, &mut got, blocks) };
                assert_eq!(ct::into_public(got), want, "sha512ext, {n} blocks");
            }
        }
    }
}
