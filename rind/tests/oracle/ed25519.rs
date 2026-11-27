//! Ed25519's independent oracle: libcrux's, HACL*'s, which rind runs
//! nowhere.
//!
//! Included as `nist.rs` is, beside it.

pub(crate) fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    let mut public = [0u8; 32];
    libcrux_ed25519::secret_to_public(&mut public, seed);
    public
}

pub(crate) fn sign(seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
    libcrux_ed25519::sign(message, seed).unwrap()
}

pub(crate) fn verify(public_key: &[u8; 32], message: &[u8], signature: &[u8]) -> bool {
    <&[u8; 64]>::try_from(signature)
        .is_ok_and(|signature| libcrux_ed25519::verify(message, public_key, signature).is_ok())
}
