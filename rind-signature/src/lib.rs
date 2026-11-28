//! `signature` 3's traits on rind: `Signer` and `Verifier` for Ed25519, ECDSA,
//! ML-DSA, and RSA.
//!
//! Each module keeps the names, paths, and re-exports of the RustCrypto crate
//! it stands in for (`ed25519_dalek`'s in [`ed25519`], `p256::ecdsa` and its
//! siblings, `ml_dsa`, `rsa`), so code written against those runs on rind by
//! naming a different crate. Every type is a thin wrapper that calls rind;
//! nothing here is a primitive or an encoding. The README lists what rind
//! cannot back.
#![no_std]

// `MultipartSigner` joins a message's parts, and a verifying key's SEC1
// encoding is boxed, as RustCrypto's are.
extern crate alloc;

mod ecdsa;
pub mod ed25519;
pub mod ml_dsa;
// RSA names its hashes with rind-digest's `sha2` types, as `rsa` does with
// `sha2`'s.
pub mod rsa;

pub use ecdsa::{p256, p384, p521};
