#![doc = include_str!("../README.md")]
// aws-lc-rs's API has these shapes, which a drop-in keeps.
#![allow(clippy::len_without_is_empty, clippy::new_without_default)]
#![warn(missing_docs, unreachable_pub)]
#![cfg_attr(docsrs, feature(doc_cfg))]

use core::fmt;

extern crate alloc;

pub mod aead;
pub mod agreement;
pub mod cipher;
pub mod constant_time;
pub mod digest;
pub mod encoding;
pub mod error;
pub mod hkdf;
pub mod hmac;
#[cfg(feature = "ring-io")]
pub mod io;
pub mod iv;
pub mod kem;
pub mod key_wrap;
pub mod pbkdf2;
pub mod pkcs8;
pub mod rand;
pub mod rsa;
pub mod signature;

mod buffer;
mod der;
mod pqdsa;
mod wipe;

/// Does nothing: rind needs no initialization. aws-lc-rs initializes AWS-LC here.
pub fn init() {}

// rind-fips builds its module only for glibc Linux on x86_64 and aarch64, as
// aws-lc-rs's FIPS build fails off its own supported platforms. A build that
// succeeded here would answer `try_fips_mode()` with a failure the caller
// asked not to get.
#[cfg(all(
    feature = "fips",
    not(all(
        target_os = "linux",
        target_env = "gnu",
        target_endian = "little",
        target_pointer_width = "64",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))
))]
compile_error!(
    "rind-aws-lc-rs's `fips` feature needs glibc Linux on little-endian x86_64 or aarch64, where rind-fips builds its module"
);

/// Fails until every approved service of the `fips` build runs in rind-fips's
/// module: aws-lc-rs's FIPS build answers `Ok` only when it does, and a build
/// that answered `Ok` with services still in rind would report FIPS mode for
/// operations outside the module's boundary. [`NOT_IN_THE_MODULE`] names what
/// is still in rind.
#[cfg(feature = "fips")]
pub fn try_fips_mode() -> Result<(), &'static str> {
    Err(NOT_IN_THE_MODULE)
}

/// What the `fips` feature has not yet moved into rind-fips's module.
#[cfg(feature = "fips")]
const NOT_IN_THE_MODULE: &str = "FIPS mode not available: the TLS record keys, HMAC, HKDF, PBKDF2, random bytes, and the constant-time compare run in rind-fips's module; digest, the other aead keys, agreement, signature, rsa, kem, and ML-DSA still run in rind";

/// Fails without the `fips` feature, since rind is then not FIPS validated.
#[cfg(not(feature = "fips"))]
pub fn try_fips_mode() -> Result<(), &'static str> {
    Err("FIPS mode not enabled!")
}

/// Always `None`: rind-fips's module has no AWS-LC module number to return.
pub fn fips_version() -> Option<u32> {
    None
}

/// Always fails: the module takes OS entropy, not AWS-LC's CPU Jitter Entropy.
pub fn try_fips_cpu_jitter_entropy() -> Result<(), &'static str> {
    Err("FIPS CPU Jitter Entropy not enabled!")
}

mod sealed {
    /// Implemented only inside rind-aws-lc-rs.
    pub trait Sealed {}
}

/// Writes bytes as lowercase hex, as aws-lc-rs's `Debug` output does.
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
