#![doc = include_str!("../README.md")]
#![no_std]
// aws-lc-rs's API has these shapes, which a drop-in keeps.
#![allow(clippy::len_without_is_empty, clippy::new_without_default)]
#![warn(missing_docs, unreachable_pub)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

use core::fmt;

extern crate alloc;
#[cfg(test)]
extern crate std;

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
mod evp;
mod pqdsa;
mod wipe;

/// Does nothing: rind needs no initialization. aws-lc-rs initializes AWS-LC here.
pub fn init() {}

/// Always fails, since rind is not FIPS validated.
pub fn try_fips_mode() -> Result<(), &'static str> {
    Err("FIPS mode not enabled!")
}

/// Always `None`, since rind is not FIPS validated.
pub fn fips_version() -> Option<u32> {
    None
}

/// Always fails, since rind is not FIPS validated.
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
