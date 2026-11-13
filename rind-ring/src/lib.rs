//! <h1 align="center">rind-ring</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">
//!
//! This crate offers [ring](https://github.com/briansmith/ring) 0.17's API, name for name, backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//! A crate on ring swaps it in by renaming its dependency, with no code
//! changes:
//!
//! ```toml
//! [dependencies]
//! ring = { package = "rind-ring", version = "0.17" }
//! ```
//!
//! Every ring feature is accepted and changes nothing.
//!
//! The rename reaches only the crate that makes it. A binary moves every crate
//! in its tree on ring 0.17 to rind, including dependencies that name ring such
//! as rustls and quinn-proto on their `ring` features, by patching ring in its
//! workspace's root `Cargo.toml` and then running `cargo update -p ring`:
//!
//! ```toml
//! [patch.crates-io]
//! ring = { git = "https://github.com/kixel-ai/rind-patch" }
//! ```
//!
//! Cargo builds the crate named `ring` in
//! [rind-patch](https://github.com/kixel-ai/rind-patch), a small repository of
//! its own, which re-exports rind-ring and accepts every ring feature.
//! crates.io has the name, so that crate is never published. Its version, 0.17.999, meets every ring
//! 0.17 requirement. Where the patch is not used, such as for an exact
//! requirement like `=0.17.14` or before the lockfile is updated, Cargo builds
//! crates.io's ring and only warns, so check that `cargo tree -i ring` prints
//! `ring v0.17.999` from rind-patch alone. A dependency on ring 0.16 or
//! older keeps it, and a library cannot patch for the binaries that use it,
//! since Cargo applies a patch only in the workspace that declares it.
//!
//! rind-ring panics wherever ring panics, such as `pbkdf2::derive` on an
//! output over (2^32 - 1) hash outputs, so its signatures match ring's
//! exactly (maintainer, 2026-10-31). rind itself never panics on caller
//! input.
//!
//! These items are not offered, so code using them, in a patched dependency
//! too, fails to build:
//!
//! - `aead::chacha20_poly1305_openssh`: rind refuses it, having no SSH consumer.
//! - `rsa::KeyPairComponents` and `rsa::KeyPair::from_components`: building a
//!   key from components means encoding its secret parts as DER, which
//!   branches on their leading bytes. Load the key as PKCS#1 or PKCS#8.
//! - `io`, `test`, `deprecated_test`, and `test_file!`: ring's DER reader and
//!   test harness, which are no cryptography. `test::rand`'s fixed random
//!   sources could not work, since rind draws its own randomness.
//!
//! And these behave differently:
//!
//! - Where ring takes a [`rand::SecureRandom`] to generate a key or sign,
//!   rind draws from the system random source itself, as
//!   [`rand::SystemRandom`], the only `SecureRandom`, does.
//! - An Ed25519 public key of small order verifies no signature, where
//!   ring verifies some that nobody made on it.
//! - A [`error::KeyRejected`]'s `Display` gives rind's reason, not ring's
//!   name for it, which ring documents as changing between releases.

// ring's API has these shapes, which a drop-in keeps.
#![allow(clippy::len_without_is_empty, clippy::new_without_default)]
#![warn(missing_docs, unreachable_pub)]

use core::fmt;

pub mod aead;
pub mod agreement;
#[doc(hidden)]
#[deprecated(note = "ring deprecates it too; compare with `hmac::verify` or a constant-time crate")]
pub mod deprecated_constant_time;
mod der;
pub mod digest;
pub mod error;
pub mod hkdf;
pub mod hmac;
pub mod pbkdf2;
pub mod pkcs8;
pub mod rand;
pub mod rsa;
pub mod signature;

#[doc(hidden)]
#[allow(deprecated)]
#[deprecated(
    note = "ring deprecates it too; compare with `hmac::verify` or a constant-time crate"
)]
pub use deprecated_constant_time as constant_time;

mod sealed {
    /// Implemented only inside rind-ring.
    pub trait Sealed {}
}

/// Writes bytes as lowercase hex, as ring's `Debug` output does.
fn write_hex(f: &mut fmt::Formatter<'_>, bytes: &[u8]) -> fmt::Result {
    bytes.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
}

/// Debugs as quoted hex.
struct Hex<'a>(&'a [u8]);

impl fmt::Debug for Hex<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("\"")?;
        write_hex(f, self.0)?;
        f.write_str("\"")
    }
}
