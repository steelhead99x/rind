//! <h1 align="center">rind-dimpl</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">
//!
//! This crate provides a [`CryptoProvider`] for [dimpl](https://github.com/algesten/dimpl), backed by [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//!
//! Build dimpl with `default-features = false`, since its default features compile aws-lc-rs.
//! Then hand the provider to each config:
//!
//! ```rust
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let config = dimpl::Config::builder()
//!     .with_crypto_provider(rind_dimpl::default_provider())
//!     .build()?;
//! # Ok(())
//! # }
//! ```
//!
//! Or install it for the process with [`CryptoProvider::install_default`].

use dimpl::crypto::CryptoProvider;

mod digest;
mod kx;
mod sign;
mod suite;

/// Returns a dimpl [`CryptoProvider`] backed by rind, with the same shape as
/// `dimpl::crypto::aws_lc_rs::default_provider()`.
///
/// AES-128-CCM-8 is not offered. ChaCha20-Poly1305 comes first where rind
/// runs AES without CPU instructions. A PEM key whose preamble starts with
/// `0` is refused.
pub fn default_provider() -> CryptoProvider {
    let (cipher_suites, dtls13_cipher_suites) = if rind::cpu::has_aes_hardware() {
        (suite::DTLS12, suite::DTLS13)
    } else {
        (suite::DTLS12_CHACHA20_FIRST, suite::DTLS13_CHACHA20_FIRST)
    };
    CryptoProvider {
        kx_groups: kx::ALL,
        signature_verification: &sign::VERIFIER,
        key_provider: &sign::KEYS,
        secure_random: &digest::RANDOM,
        hash_provider: &digest::HASH,
        hmac_provider: &digest::HMAC,
        cipher_suites,
        dtls13_cipher_suites,
    }
}
