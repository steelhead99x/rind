//! Password-based key derivation with PBKDF2 (RFC 8018).

use core::num::NonZeroU32;

use crate::{digest, error, hmac};

/// A PBKDF2 algorithm, chosen by one of this module's constants.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Algorithm(hmac::Algorithm);

impl Algorithm {
    /// The module's algorithm, or `None` for SHA-1, which it does not approve.
    #[cfg(feature = "fips")]
    fn module(&self) -> Option<&'static rind_fips::pbkdf2::Algorithm> {
        use digest::AlgorithmId::*;
        match self.0.digest_algorithm().id {
            SHA256 => Some(&rind_fips::pbkdf2::PBKDF2_HMAC_SHA256),
            SHA384 => Some(&rind_fips::pbkdf2::PBKDF2_HMAC_SHA384),
            SHA512 => Some(&rind_fips::pbkdf2::PBKDF2_HMAC_SHA512),
            _ => None,
        }
    }

    fn rind(&self) -> &'static rind::pbkdf2::Algorithm {
        use digest::AlgorithmId::*;
        match self.0.digest_algorithm().id {
            SHA1 => &rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
            SHA256 => &rind::pbkdf2::PBKDF2_HMAC_SHA256,
            SHA384 => &rind::pbkdf2::PBKDF2_HMAC_SHA384,
            SHA512 => &rind::pbkdf2::PBKDF2_HMAC_SHA512,
            SHA512_256 | SHA3_256 | SHA3_384 | SHA3_512 => {
                unreachable!("only this module's constants make an Algorithm")
            }
        }
    }
}

/// PBKDF2 with HMAC-SHA1.
pub const PBKDF2_HMAC_SHA1: Algorithm = Algorithm(hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY);

/// PBKDF2 with HMAC-SHA256.
pub const PBKDF2_HMAC_SHA256: Algorithm = Algorithm(hmac::HMAC_SHA256);

/// PBKDF2 with HMAC-SHA384.
pub const PBKDF2_HMAC_SHA384: Algorithm = Algorithm(hmac::HMAC_SHA384);

/// PBKDF2 with HMAC-SHA512.
pub const PBKDF2_HMAC_SHA512: Algorithm = Algorithm(hmac::HMAC_SHA512);

/// The module for a derivation SP 800-132 approves, which it refuses
/// otherwise: a secret of at least 14 bytes, a salt of at least 16, at least
/// 1000 iterations, and an `out` of at least 14 bytes. Decided from the
/// arguments, not by trying the module, so rind runs exactly the rest.
#[cfg(feature = "fips")]
fn approved(
    algorithm: Algorithm,
    iterations: NonZeroU32,
    salt: &[u8],
    secret: &[u8],
    out_len: usize,
) -> Option<&'static rind_fips::pbkdf2::Algorithm> {
    if secret.len() >= 14 && salt.len() >= 16 && iterations.get() >= 1000 && out_len >= 14 {
        algorithm.module()
    } else {
        None
    }
}

/// Fills `out` with the key derived from `secret` and `salt` over `iterations` rounds.
///
/// # Panics
///
/// Panics if `out` is longer than PBKDF2 allows, (2^32 - 1) hash outputs, as
/// aws-lc-rs does.
pub fn derive(
    algorithm: Algorithm,
    iterations: NonZeroU32,
    salt: &[u8],
    secret: &[u8],
    out: &mut [u8],
) {
    if out.is_empty() {
        return;
    }
    #[cfg(feature = "fips")]
    if let Some(module) = approved(algorithm, iterations, salt, secret, out.len()) {
        rind_fips::pbkdf2::Secret::new(module, secret)
            .derive(iterations, salt, out)
            .expect("derived key too long");
        return;
    }
    rind::pbkdf2::Secret::new(algorithm.rind(), secret)
        .derive(iterations, salt, out)
        .expect("derived key too long");
}

/// Checks in constant time that `previously_derived` is what [`derive()`] makes for the same inputs.
///
/// Fails if `previously_derived` is empty or differs. As in aws-lc-rs, a
/// value shorter than the hash output is compared too. Unlike aws-lc-rs,
/// it also fails, rather than panicking, when `previously_derived` is longer
/// than PBKDF2 allows.
pub fn verify(
    algorithm: Algorithm,
    iterations: NonZeroU32,
    salt: &[u8],
    secret: &[u8],
    previously_derived: &[u8],
) -> Result<(), error::Unspecified> {
    #[cfg(feature = "fips")]
    if previously_derived.len() >= algorithm.0.tag_len()
        && let Some(module) = approved(
            algorithm,
            iterations,
            salt,
            secret,
            previously_derived.len(),
        )
    {
        return rind_fips::pbkdf2::Secret::new(module, secret)
            .verify(iterations, salt, previously_derived)
            .map_err(error::unspecified);
    }
    let secret = rind::pbkdf2::Secret::new(algorithm.rind(), secret);
    let hash_len = algorithm.0.tag_len();
    if previously_derived.len() >= hash_len {
        return secret
            .verify(iterations, salt, previously_derived)
            .map_err(error::unspecified);
    }
    if previously_derived.is_empty() {
        return Err(error::Unspecified);
    }

    // rind refuses a value this short, so derive its block and compare here.
    let mut derived = [0u8; digest::MAX_OUTPUT_LEN];
    let derived = &mut derived[..previously_derived.len()];
    secret
        .derive(iterations, salt, derived)
        .map_err(error::unspecified)?;
    rind::constant_time::verify(derived, previously_derived).map_err(error::unspecified)
}
