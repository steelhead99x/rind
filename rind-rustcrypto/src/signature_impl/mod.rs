//! `signature` 3's traits over rind's signatures.

pub mod ecdsa;
pub mod ed25519;
pub mod ml_dsa;
// RSA names its hashes with this crate's `sha2` types.
#[cfg(feature = "digest-0_11")]
pub mod rsa;
