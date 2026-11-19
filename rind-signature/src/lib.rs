//! `signature` 3's traits on rind: `Signer` and `Verifier` for Ed25519, ECDSA,
//! ML-DSA, and RSA.
//!
//! Each module mirrors the RustCrypto crate it stands in for (`ed25519_dalek`'s
//! names in [`ed25519`], `p256::ecdsa` and its siblings, `ml_dsa`, `rsa`), so
//! code generic over those traits runs on rind by naming a different type.
//! Every type is a thin wrapper that calls rind; nothing here is a primitive or
//! an encoding. The README lists what rind cannot back.

mod ecdsa;
pub mod ed25519;
pub mod ml_dsa;
// RSA names its hashes with rind-digest's `sha2` types, as `rsa` does with
// `sha2`'s.
pub mod rsa;

pub use ecdsa::{p256, p384, p521};
