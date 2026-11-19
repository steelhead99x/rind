// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! GHASH with NEON's 8-bit polynomial multiply, for CPUs without the crypto
//! extension, using aws-lc's `ghash-armv4` routines.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. It is not
//! formally verified: its correctness rests on its use and testing in OpenSSL,
//! BoringSSL, and aws-lc, and on rind's tests of it against the portable code,
//! Wycheproof, and aws-lc-rs.

use super::cpu::HaveNeon;
use crate::low;

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("gcm_init_neon")]
    fn gcm_init_neon(htable: *mut NeonTable, h: *const [u64; 2]);

    #[link_name = aws_lc_symbol!("gcm_ghash_neon")]
    fn gcm_ghash_neon(xi: *mut [u8; 16], htable: *const NeonTable, input: *const u8, len: usize);
}

// As in `aesv8_armx`: ARM mode with NEON, then the target's `.fpu` again.
core::arch::global_asm!(
    ".text",
    ".fpu neon",
    ".code 32",
    include_str!("aws_lc/ghash-armv4.s"),
    ".fpu vfpv3",
    gcm_init_neon = sym gcm_init_neon,
    gcm_ghash_neon = sym gcm_ghash_neon,
);

/// The twisted GHASH key, which `gcm_init_neon` writes into the first entry of
/// aws-lc's `u128 Htable[16]` and is all `gcm_ghash_neon` reads.
#[repr(C, align(16))]
pub(crate) struct NeonTable([u64; 2]);

impl NeonTable {
    /// Precomputes for the GHASH key `h`, AES's encryption of the zero block.
    pub(crate) fn new(h: &[u8; 16], _: HaveNeon) -> Self {
        let (hi, lo) = h.split_at(8);
        let h = [
            u64::from_be_bytes(hi.try_into().unwrap()),
            u64::from_be_bytes(lo.try_into().unwrap()),
        ];
        let mut r = Self([0; 2]);
        // SAFETY: `r` has room for the one entry the routine writes and `h` is
        // two words. The token proves the
        // CPU has NEON.
        unsafe { asm_call!(unsafe extern "C" gcm_init_neon(&mut r, &h)) };
        r
    }

    /// Folds whole blocks of `input` into the GHASH state `xi`.
    pub(crate) fn ghash(&self, xi: &mut [u8; 16], input: &[[u8; 16]]) {
        // aws-lc loads the first block before checking the length.
        if input.is_empty() {
            return;
        }
        // SAFETY: `input` is `size_of_val(input)` readable bytes, a multiple
        // of 16. Only a `HaveNeon` token builds `self`.
        unsafe {
            asm_call!(unsafe extern "C" gcm_ghash_neon(xi, self, input.as_ptr().cast(), size_of_val(input)))
        }
    }
}

impl Drop for NeonTable {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for NeonTable {}
