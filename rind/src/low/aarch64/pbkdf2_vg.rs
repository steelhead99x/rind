// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! PBKDF2 on pyca/verified-garbage's proven routines (`super::vg`).
//!
//! Each routine is RFC 8018's whole PBKDF2 over HMAC, keying included: VG
//! proves no routine below it, and its single HMAC measured slower than
//! rind's at short messages, so its win is the iteration loop it runs
//! between them. Each runs on its hash's instructions: the crypto
//! extension's for SHA-1 and SHA-256, the SHA-512 instructions for SHA-384
//! and SHA-512.

use core::num::NonZeroU32;

use super::cpu::{HaveCryptoExt, HaveSha3};
use super::vg;

/// One hash's VG routine, which this CPU runs: only its constructors make
/// one, after checking the CPU.
pub(crate) struct Pbkdf2 {
    routine: unsafe extern "C" fn(*const u8, usize, *const u8, usize, u32, *mut u8, usize),
    hash_len: usize,
}

static SHA1: Pbkdf2 = Pbkdf2 {
    routine: vg::vg_pbkdf2_hmac_sha1_sha2::vg_pbkdf2_hmac_sha1_sha2,
    hash_len: 20,
};

static SHA256: Pbkdf2 = Pbkdf2 {
    routine: vg::vg_pbkdf2_hmac_sha256_sha2::vg_pbkdf2_hmac_sha256_sha2,
    hash_len: 32,
};

static SHA384: Pbkdf2 = Pbkdf2 {
    routine: vg::vg_pbkdf2_hmac_sha384_sha512::vg_pbkdf2_hmac_sha384_sha512,
    hash_len: 48,
};

static SHA512: Pbkdf2 = Pbkdf2 {
    routine: vg::vg_pbkdf2_hmac_sha512_sha512::vg_pbkdf2_hmac_sha512_sha512,
    hash_len: 64,
};

impl Pbkdf2 {
    /// PBKDF2-HMAC-SHA1, if the CPU has the crypto extension.
    pub(crate) fn sha1() -> Option<&'static Self> {
        HaveCryptoExt::check().map(|_| &SHA1)
    }

    /// PBKDF2-HMAC-SHA256, if the CPU has the crypto extension.
    pub(crate) fn sha256() -> Option<&'static Self> {
        HaveCryptoExt::check().map(|_| &SHA256)
    }

    /// PBKDF2-HMAC-SHA384, if the CPU has the SHA-512 instructions.
    pub(crate) fn sha384() -> Option<&'static Self> {
        HaveSha3::check().map(|_| &SHA384)
    }

    /// PBKDF2-HMAC-SHA512, if the CPU has the SHA-512 instructions.
    pub(crate) fn sha512() -> Option<&'static Self> {
        HaveSha3::check().map(|_| &SHA512)
    }

    /// Fills `out` with the key PBKDF2 derives from `password` and `salt`
    /// over `iterations` rounds.
    ///
    /// Panics if `out` needs more than RFC 8018's 2^32 - 1 blocks, which
    /// callers refuse first.
    pub(crate) fn derive(
        &self,
        password: &[u8],
        salt: &[u8],
        iterations: NonZeroU32,
        out: &mut [u8],
    ) {
        // By multiplying, not dividing, so `admin/ct-vartime` finds no
        // division.
        assert!(
            self.hash_len
                .checked_mul(u32::MAX as usize)
                .is_none_or(|most| out.len() <= most)
        );
        // SAFETY: each slice is a distinct Rust object valid for its length,
        // so none overlaps another, the stack, or the end of the address
        // space; `iterations` is positive and `out` at most 2^32 - 1 blocks,
        // as just checked; and the constructor checked that the CPU has the
        // instructions the routine needs.
        unsafe {
            (self.routine)(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                salt.len(),
                iterations.get(),
                out.as_mut_ptr(),
                out.len(),
            )
        }
    }
}
