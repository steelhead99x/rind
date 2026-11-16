//! Key derivation with HKDF (RFC 5869), over any [`hmac`] algorithm.
//!
//! HKDF-Expand is rind's. HKDF-Extract is its HMAC keyed by the salt, as
//! ring's `extract` cannot fail and a [`Salt`] can be made from key material.

use core::fmt;

use crate::{digest, error, hmac};

/// An HKDF algorithm, chosen by one of this module's statics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Algorithm(hmac::Algorithm);

impl Algorithm {
    /// The HMAC algorithm this HKDF is built on.
    pub fn hmac_algorithm(&self) -> hmac::Algorithm {
        self.0
    }

    fn rind(&self) -> &'static rind::hkdf::Algorithm {
        // Each of this module's statics has a hash of its own output length.
        match self.len() {
            20 => &rind::hkdf::legacy::HKDF_SHA1,
            32 => &rind::hkdf::HKDF_SHA256,
            48 => &rind::hkdf::HKDF_SHA384,
            64 => &rind::hkdf::HKDF_SHA512,
            _ => unreachable!("only this module's statics make an Algorithm"),
        }
    }
}

/// HKDF-SHA1, for legacy protocols only.
pub static HKDF_SHA1_FOR_LEGACY_USE_ONLY: Algorithm =
    Algorithm(hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY);

/// HKDF-SHA256.
pub static HKDF_SHA256: Algorithm = Algorithm(hmac::HMAC_SHA256);

/// HKDF-SHA384.
pub static HKDF_SHA384: Algorithm = Algorithm(hmac::HMAC_SHA384);

/// HKDF-SHA512.
pub static HKDF_SHA512: Algorithm = Algorithm(hmac::HMAC_SHA512);

/// An HKDF key, such as a [`Salt`] or [`Prk`], is as long as the hash's output.
impl KeyType for Algorithm {
    fn len(&self) -> usize {
        self.0.digest_algorithm().output_len()
    }
}

/// A salt, keyed once and reused for every secret it extracts from.
#[derive(Debug)]
pub struct Salt(hmac::Key);

impl Salt {
    /// Keys `algorithm` with `value`; an empty `value` is RFC 5869's absent salt.
    pub fn new(algorithm: Algorithm, value: &[u8]) -> Self {
        Self(hmac::Key::new(algorithm.0, value))
    }

    /// Extracts a pseudorandom key from `secret` (HKDF-Extract).
    pub fn extract(&self, secret: &[u8]) -> Prk {
        let prk = hmac::sign(&self.0, secret);
        Prk::new_less_safe(self.algorithm(), prk.as_ref())
    }

    /// The algorithm this salt was made for.
    pub fn algorithm(&self) -> Algorithm {
        Algorithm(self.0.algorithm())
    }
}

impl From<Okm<'_, Algorithm>> for Salt {
    fn from(okm: Okm<'_, Algorithm>) -> Self {
        Self(hmac::Key::from(okm.into_hmac()))
    }
}

/// The length of what an [`Okm`] becomes.
pub trait KeyType {
    /// The length, in bytes.
    fn len(&self) -> usize;
}

/// A pseudorandom key, from which [`Prk::expand`] derives any number of keys.
#[derive(Clone)]
pub struct Prk {
    inner: rind::hkdf::Prk,
    algorithm: Algorithm,
}

impl Prk {
    /// Takes `value` as the pseudorandom key itself, skipping HKDF-Extract.
    pub fn new_less_safe(algorithm: Algorithm, value: &[u8]) -> Self {
        Self {
            inner: rind::hkdf::Prk::new(algorithm.rind(), value),
            algorithm,
        }
    }

    /// Derives key material for the concatenation of `info` (HKDF-Expand),
    /// failing if `len` is over 255 hash outputs.
    pub fn expand<'a, L: KeyType>(
        &'a self,
        info: &'a [&'a [u8]],
        len: L,
    ) -> Result<Okm<'a, L>, error::Unspecified> {
        let len_cached = len.len();
        if len_cached > 255 * self.algorithm.len() {
            return Err(error::Unspecified);
        }
        Ok(Okm {
            prk: self,
            info,
            len,
            len_cached,
        })
    }
}

// As ring's, which holds an HMAC key.
impl fmt::Debug for Prk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Key(&'static digest::Algorithm);
        impl fmt::Debug for Key {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct("Key").field("algorithm", self.0).finish()
            }
        }
        let digest = self.algorithm.0.digest_algorithm();
        f.debug_tuple("Prk").field(&Key(digest)).finish()
    }
}

impl From<Okm<'_, Algorithm>> for Prk {
    fn from(okm: Okm<'_, Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut key = [0u8; digest::MAX_OUTPUT_LEN];
        let key = &mut key[..algorithm.len()];
        okm.fill_exact(key);
        Self::new_less_safe(algorithm, key)
    }
}

/// Key material from [`Prk::expand`], as long as `L` says, for [`Okm::fill`] or a key's `From`.
#[derive(Debug)]
pub struct Okm<'a, L: KeyType> {
    prk: &'a Prk,
    info: &'a [&'a [u8]],
    len: L,
    len_cached: usize,
}

impl<L: KeyType> Okm<'_, L> {
    /// What this key material becomes.
    pub fn len(&self) -> &L {
        &self.len
    }

    /// Fills `out`, failing unless it is exactly the length `L` says.
    pub fn fill(self, out: &mut [u8]) -> Result<(), error::Unspecified> {
        if out.len() != self.len_cached {
            return Err(error::Unspecified);
        }
        self.prk
            .inner
            .fill(self.info, out)
            .map_err(|_| error::Unspecified)
    }

    /// Fills `out`, which the caller made exactly the length `L` says.
    pub(crate) fn fill_exact(self, out: &mut [u8]) {
        self.fill(out)
            .expect("`expand` held the length to 255 hash outputs");
    }
}

impl<'a> Okm<'a, Algorithm> {
    fn into_hmac(self) -> Okm<'a, hmac::Algorithm> {
        Okm {
            prk: self.prk,
            info: self.info,
            len: self.len.0,
            len_cached: self.len_cached,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ring derives `Debug` for `Prk(hmac::Key)`, whose `Debug` is a `debug_struct`.
    #[test]
    fn prk_debug_matches_ring() {
        let prk = Prk::new_less_safe(HKDF_SHA256, &[0; 32]);
        assert_eq!(format!("{prk:?}"), "Prk(Key { algorithm: SHA256 })");
        assert_eq!(
            format!("{prk:#?}"),
            "Prk(\n    Key {\n        algorithm: SHA256,\n    },\n)"
        );
    }
}
