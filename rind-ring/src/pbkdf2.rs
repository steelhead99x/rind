//! Password-based key derivation with PBKDF2 (RFC 8018).

use core::num::NonZeroU32;

use crate::{digest, error, hmac};

/// A PBKDF2 algorithm, chosen by one of this module's statics.
#[derive(Clone, Copy)]
pub struct Algorithm {
    hmac: hmac::Algorithm,
    rind: &'static rind::pbkdf2::Algorithm,
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.hmac == other.hmac
    }
}

impl Eq for Algorithm {}

/// PBKDF2 with HMAC-SHA1.
pub static PBKDF2_HMAC_SHA1: Algorithm = Algorithm {
    hmac: hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
    rind: &rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
};

/// PBKDF2 with HMAC-SHA256.
pub static PBKDF2_HMAC_SHA256: Algorithm = Algorithm {
    hmac: hmac::HMAC_SHA256,
    rind: &rind::pbkdf2::PBKDF2_HMAC_SHA256,
};

/// PBKDF2 with HMAC-SHA384.
pub static PBKDF2_HMAC_SHA384: Algorithm = Algorithm {
    hmac: hmac::HMAC_SHA384,
    rind: &rind::pbkdf2::PBKDF2_HMAC_SHA384,
};

/// PBKDF2 with HMAC-SHA512.
pub static PBKDF2_HMAC_SHA512: Algorithm = Algorithm {
    hmac: hmac::HMAC_SHA512,
    rind: &rind::pbkdf2::PBKDF2_HMAC_SHA512,
};

/// Fills `out` with the key derived from `secret` and `salt` over `iterations` rounds.
///
/// # Panics
///
/// Panics if `out` is longer than PBKDF2 allows, (2^32 - 1) hash outputs, as
/// ring does.
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
    rind::pbkdf2::Secret::new(algorithm.rind, secret)
        .derive(iterations, salt, out)
        .expect("PBKDF2 output over (2^32 - 1) hash outputs");
}

/// Checks in constant time that `previously_derived` is what [`derive()`] makes for the same inputs.
///
/// Fails if `previously_derived` is empty or differs. As in ring, a value
/// shorter than the hash output is compared too.
pub fn verify(
    algorithm: Algorithm,
    iterations: NonZeroU32,
    salt: &[u8],
    secret: &[u8],
    previously_derived: &[u8],
) -> Result<(), error::Unspecified> {
    let secret = rind::pbkdf2::Secret::new(algorithm.rind, secret);
    let hash_len = algorithm.hmac.digest_algorithm().output_len();
    if previously_derived.len() >= hash_len {
        return secret
            .verify(iterations, salt, previously_derived)
            .map_err(|_| error::Unspecified);
    }
    if previously_derived.is_empty() {
        return Err(error::Unspecified);
    }

    // rind refuses a value this short, so derive its block and compare here.
    let mut derived = [0u8; digest::MAX_OUTPUT_LEN];
    let derived = &mut derived[..previously_derived.len()];
    secret
        .derive(iterations, salt, derived)
        .map_err(|_| error::Unspecified)?;
    rind::constant_time::verify(derived, previously_derived).map_err(|_| error::Unspecified)
}
