// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

#![deny(unsafe_code)]

// libcrux exposes whole operations rather than the field and bignum
// arithmetic these build on, so the portable backend, which armv7 builds on,
// swaps them at this layer. cargo-mutants follows `path` but not `cfg_attr`.
// See UPSTREAM.md, "cargo-mutants cannot see into `cfg_if!`".
#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
pub(super) mod aes_gcm;
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
#[path = "portable/aes_gcm.rs"]
pub(super) mod aes_gcm;
#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
pub(super) mod ed25519;
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
#[path = "portable/ed25519.rs"]
pub(super) mod ed25519;
#[cfg_attr(
    any(rind_backend = "arm", rind_backend = "portable"),
    path = "portable/ristretto255.rs"
)]
pub(super) mod ristretto255;

pub(super) mod aes;
pub(super) mod aes_cbc;
pub(super) mod aes_kw;
pub(super) mod chacha20;
pub(super) mod chacha20poly1305;
#[cfg_attr(
    any(rind_backend = "arm", rind_backend = "portable"),
    path = "portable/edwards25519.rs"
)]
pub(super) mod edwards25519;
pub(super) mod hash_to_curve;
pub(super) mod md5;
pub(super) mod mldsa;
pub(super) mod mlkem768;
pub(super) mod p256;
pub(super) mod p384;
pub(super) mod p521;
#[cfg(test)]
mod ristretto255_tests;
pub(super) mod rng;
pub(super) mod rsa_key_size;
pub(super) mod rsa_priv;
pub(super) mod rsa_pub;
pub(super) mod sha1;
pub(super) mod sha2;
pub(super) mod sha3;
pub(super) mod util;
pub(super) mod x25519;
pub(super) mod xchacha20poly1305;
