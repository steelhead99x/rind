// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable backend: pure Rust, for every architecture without one of
//! rind's assembly backends, and the base armv7 builds on. Most is libcrux's
//! and HACL*'s, where whole operations are swapped in `mid`, and rind's own
//! portable arithmetic in `generic`: the NIST curves, RSA, and ML-KEM. Each
//! file names its source.
//!
//! It needs no CPU features, and each operation's time depends on no secret,
//! given a CPU whose multiply takes the same time for every operand.

pub(crate) mod aes;
pub(crate) mod aes_cbc;
pub(crate) mod aes_ctr;
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
