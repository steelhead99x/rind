// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512 on the unrolled body in `generic::sha512`.
//!
//! The SHA512-instruction and AVX2 assembly this replaced is not what a
//! `core::arch` intrinsic sequence can be checked against on this crate's
//! usual hosts: the SHA512 instructions are absent from the CPUs the tests
//! run on, and an AVX2 schedule that interleaves two blocks is a separate
//! program from the FIPS round. The unrolled scalar body is the one the
//! tests execute.

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
}
