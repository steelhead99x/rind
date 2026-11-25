// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable backend: pure Rust, for every architecture without one of
//! rind's assembly backends, and the base armv7 builds on. Most is libcrux's
//! and HACL*'s, where whole operations are swapped in `mid`, and rind's own
//! portable code in `generic`: the NIST curves, RSA, ML-KEM, and SHA-2. Each
//! file names its source.
//!
//! It needs no CPU features, and each operation's time depends on no secret,
//! given a CPU whose multiply takes the same time for every operand.

pub(crate) mod aes;
pub(crate) mod aes_cbc;
pub(crate) mod aes_ctr;
// Fixsliced AES on portable riscv32 targets (measured on the ESP32-C6),
// aws-lc's bitsliced AES elsewhere; tests build both, to check one against the
// other.
#[cfg(any(all(rind_backend = "portable", target_arch = "riscv32"), test))]
#[path = "../generic/aes_fixslice32.rs"]
mod aes_fixslice32;
#[cfg(any(not(all(rind_backend = "portable", target_arch = "riscv32")), test))]
#[path = "../generic/aes_nohw.rs"]
mod aes_nohw;
pub(crate) mod bignum_eq;
#[cfg(rind_backend = "portable")]
pub(crate) mod chacha20;
#[cfg(rind_backend = "portable")]
pub(crate) mod cpu;
pub(crate) mod curve25519;
#[path = "../generic/ghash_nohw.rs"]
pub(crate) mod ghash_nohw;
#[cfg(rind_backend = "portable")]
pub(crate) mod keccak;
pub(crate) mod poly1305;
#[cfg(rind_backend = "portable")]
pub(crate) mod sha;
#[cfg(any(all(rind_backend = "portable", target_arch = "riscv32"), test))]
#[path = "../generic/words32.rs"]
mod words32;
