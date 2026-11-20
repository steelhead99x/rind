//! Ed25519's independent oracle: libcrux's, HACL*'s, except on the
//! portable backend, whose SHA-512 is HACL*'s too, where it is the
//! textbook reference.
//!
//! Included as `nist.rs` is, beside it.

#[cfg(not(rind_backend = "portable"))]
pub(crate) fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    let mut public = [0u8; 32];
    libcrux_ed25519::secret_to_public(&mut public, seed);
    public
}

#[cfg(not(rind_backend = "portable"))]
pub(crate) fn sign(seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
    libcrux_ed25519::sign(message, seed).unwrap()
}

#[cfg(not(rind_backend = "portable"))]
pub(crate) fn verify(public_key: &[u8; 32], message: &[u8], signature: &[u8]) -> bool {
    <&[u8; 64]>::try_from(signature)
        .is_ok_and(|signature| libcrux_ed25519::verify(message, public_key, signature).is_ok())
}

#[cfg(rind_backend = "portable")]
pub(crate) fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    super::reference::edwards25519().ed25519_public_key(seed)
}

#[cfg(rind_backend = "portable")]
pub(crate) fn sign(seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
    super::reference::edwards25519().ed25519_sign(seed, message)
}

#[cfg(rind_backend = "portable")]
pub(crate) fn verify(public_key: &[u8; 32], message: &[u8], signature: &[u8]) -> bool {
    super::reference::edwards25519().ed25519_verify(public_key, message, signature)
}
