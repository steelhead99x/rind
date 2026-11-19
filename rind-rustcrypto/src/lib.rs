//! RustCrypto's traits on rind.
//!
//! Each module mirrors the RustCrypto crate it stands in for (`sha2`, `sha3`,
//! `hmac`, and so on), and each trait crate and version it implements is a
//! cargo feature (`digest-0_11`, `aead-0_6`, ...), so code generic over those
//! traits runs on rind by naming a different type. Every type is a thin
//! wrapper that calls rind; nothing here is a primitive or an encoding. The
//! README lists what rind cannot back.

#[cfg(feature = "digest-0_11")]
mod digest_impl;
#[cfg(feature = "digest-0_11")]
pub use digest_impl::{hmac, sha2, sha3};

#[cfg(feature = "aead-0_6")]
mod aead_impl;
#[cfg(feature = "aead-0_6")]
pub use aead_impl::{aes_gcm, chacha20poly1305};

#[cfg(feature = "signature-3")]
mod signature_impl;
#[cfg(feature = "signature-3")]
pub use signature_impl::ecdsa::{p256, p384, p521};
#[cfg(feature = "signature-3")]
pub use signature_impl::ed25519;
#[cfg(feature = "signature-3")]
pub use signature_impl::ml_dsa;
