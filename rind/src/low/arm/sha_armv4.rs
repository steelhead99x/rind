// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1, SHA-256, and SHA-512 compression with aws-lc's `sha1-armv4-large`,
//! `sha256-armv4`, and `sha512-armv4` routines: the AArch32 crypto extension's
//! for SHA-1 and SHA-256 where the CPU has it, else NEON where it has that,
//! and integer code otherwise.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. It is not
//! formally verified: its correctness rests on its use and testing in OpenSSL,
//! BoringSSL, and aws-lc, and on rind's tests of it against the portable code,
//! CAVP, and aws-lc-rs.

use super::cpu::{HaveCryptoExt, HaveNeon};

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("sha1_block_data_order_nohw")]
    fn sha1_block_data_order_nohw(state: *mut [u32; 5], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha1_block_data_order_neon")]
    fn sha1_block_data_order_neon(state: *mut [u32; 5], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha1_block_data_order_hw")]
    fn sha1_block_data_order_hw(state: *mut [u32; 5], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha256_block_data_order_nohw")]
    fn sha256_block_data_order_nohw(state: *mut [u32; 8], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha256_block_data_order_neon")]
    fn sha256_block_data_order_neon(state: *mut [u32; 8], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha256_block_data_order_hw")]
    fn sha256_block_data_order_hw(state: *mut [u32; 8], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha512_block_data_order_nohw")]
    fn sha512_block_data_order_nohw(state: *mut [u64; 8], data: *const u8, blocks: usize);

    #[link_name = aws_lc_symbol!("sha512_block_data_order_neon")]
    fn sha512_block_data_order_neon(state: *mut [u64; 8], data: *const u8, blocks: usize);
}

// As in `aesv8_armx`: ARM mode with NEON, then the target's `.fpu` again.
core::arch::global_asm!(
    ".text",
    ".fpu neon",
    ".code 32",
    include_str!("aws_lc/sha1-armv4-large.s"),
    include_str!("aws_lc/sha256-armv4.s"),
    include_str!("aws_lc/sha512-armv4.s"),
    ".fpu vfpv3",
    sha1_block_data_order_nohw = sym sha1_block_data_order_nohw,
    sha1_block_data_order_neon = sym sha1_block_data_order_neon,
    sha1_block_data_order_hw = sym sha1_block_data_order_hw,
    sha256_block_data_order_nohw = sym sha256_block_data_order_nohw,
    sha256_block_data_order_neon = sym sha256_block_data_order_neon,
    sha256_block_data_order_hw = sym sha256_block_data_order_hw,
    sha512_block_data_order_nohw = sym sha512_block_data_order_nohw,
    sha512_block_data_order_neon = sym sha512_block_data_order_neon,
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
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    if !blocks.is_empty() {
        sha1_compress_blocks(state, blocks);
    }
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    // As in `sha1_compress_blocks`.
    if blocks.is_empty() {
        return;
    }
    let (data, num) = (blocks.as_ptr(), blocks.len() / 64);
    if HaveCryptoExt::check().is_some() {
        // SAFETY: `blocks` is `num` readable blocks, and the token proves the
        // CPU has the SHA-256 instructions.
        unsafe { asm_call!(unsafe extern "C" sha256_block_data_order_hw(state, data, num)) }
    } else if HaveNeon::check().is_some() {
        // SAFETY: `blocks` is `num` readable blocks, and the token proves the
        // CPU has NEON.
        unsafe { asm_call!(unsafe extern "C" sha256_block_data_order_neon(state, data, num)) }
    } else {
        // SAFETY: `blocks` is `num` readable blocks.
        unsafe { asm_call!(unsafe extern "C" sha256_block_data_order_nohw(state, data, num)) }
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

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // Both routines run their loop at least once, so zero blocks would read
    // past `blocks`.
    if blocks.is_empty() {
        return;
    }
    let (data, num) = (blocks.as_ptr(), blocks.len() / 128);
    match HaveNeon::check() {
        // SAFETY: `blocks` is `num` readable blocks, and the token proves the
        // CPU has NEON.
        Some(_) => unsafe {
            asm_call!(unsafe extern "C" sha512_block_data_order_neon(state, data, num))
        },
        // SAFETY: `blocks` is `num` readable blocks.
        None => unsafe {
            asm_call!(unsafe extern "C" sha512_block_data_order_nohw(state, data, num))
        },
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::generic;

    // Every other test sees only the path the CPU picks, so each SHA-1 and
    // SHA-256 routine the CPU can run is checked against the portable code
    // here: odd and even block counts, with distinct bytes in every block.
    #[test]
    fn asm_matches_portable() {
        type Sha1 = unsafe extern "C" fn(*mut [u32; 5], *const u8, usize);
        type Sha256 = unsafe extern "C" fn(*mut [u32; 8], *const u8, usize);
        let mut routines: Vec<(&str, Sha1, Sha256)> = vec![(
            "nohw",
            sha1_block_data_order_nohw,
            sha256_block_data_order_nohw,
        )];
        if HaveNeon::check().is_some() {
            routines.push((
                "neon",
                sha1_block_data_order_neon,
                sha256_block_data_order_neon,
            ));
        }
        if HaveCryptoExt::check().is_some() {
            routines.push(("hw", sha1_block_data_order_hw, sha256_block_data_order_hw));
        }
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for (name, sha1, sha256) in routines {
            for n in 1..=5 {
                let blocks = &blocks[..n * 64];

                let mut want = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
                let mut got = want;
                generic::sha1::sha1_compress_blocks(&mut want, blocks);
                // SAFETY: `blocks` is `n` blocks, and the CPU has what the
                // routine needs.
                unsafe { asm_call!(unsafe extern "C" sha1(&mut got, blocks.as_ptr(), n)) };
                assert_eq!(got, want, "sha1 {name}, {n} blocks");

                let mut want = [
                    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
                    0x1f83d9ab, 0x5be0cd19,
                ];
                let mut got = want;
                generic::sha256::sha256_compress_blocks(&mut want, blocks);
                // SAFETY: as above.
                unsafe { asm_call!(unsafe extern "C" sha256(&mut got, blocks.as_ptr(), n)) };
                assert_eq!(got, want, "sha256 {name}, {n} blocks");
            }
        }
    }

    // Likewise for SHA-512's two routines, against each other.
    #[test]
    fn sha512_neon_matches_nohw() {
        if HaveNeon::check().is_none() {
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
            // SAFETY: `blocks` holds at least `n` blocks, and the CPU has NEON.
            unsafe {
                asm_call!(unsafe extern "C" sha512_block_data_order_nohw(&mut want, blocks.as_ptr(), n));
                asm_call!(unsafe extern "C" sha512_block_data_order_neon(&mut got, blocks.as_ptr(), n));
            }
            assert_eq!(got, want, "{n} blocks");
        }
    }
}
