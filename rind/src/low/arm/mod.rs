// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! 32-bit ARM: the portable ChaCha20, SHA, and Poly1305 bodies, with aws-lc's
//! assembly for RSA's Montgomery multiplication and the ARMv8 crypto
//! extension where the CPU has it, BoringSSL's for X25519 where the CPU has
//! NEON, and OpenSSL's for Keccak-f.

/// The symbol for an aws-lc routine, qualified by rind's version so two
/// semver-incompatible copies of rind can link into one binary.
macro_rules! aws_lc_symbol {
    ($name:literal) => {
        concat!(
            "rind_",
            env!("CARGO_PKG_VERSION_MAJOR"),
            "_",
            env!("CARGO_PKG_VERSION_MINOR"),
            "_",
            env!("CARGO_PKG_VERSION_PATCH"),
            "_",
            $name
        )
    };
}

pub(crate) mod aes;
pub(crate) mod aes_cbc;
pub(crate) mod aes_ctr;
pub(crate) mod aesv8_armx;
pub(crate) mod chacha20;
pub(crate) mod cpu;
#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) mod ct_qemu;
pub(crate) mod curve25519;
pub(crate) mod ghashv8_armx;
pub(crate) mod keccak1600_armv4;
pub(crate) mod mont;
pub(crate) mod poly1305;
pub(crate) mod sha_armv4;
