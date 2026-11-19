//! Key derivation with HKDF (RFC 5869), over any [`hmac`] algorithm.
//!
//! HKDF-Expand is rind's. HKDF-Extract is its HMAC keyed by the salt, as
//! aws-lc-rs's `extract` cannot fail and a [`Salt`] can be made from key
//! material.

use core::fmt;

use crate::wipe::Wiped;
use crate::{digest, error, hmac};

/// An HKDF algorithm, chosen by one of this module's constants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Algorithm(hmac::Algorithm);

impl Algorithm {
    /// The HMAC algorithm this HKDF is built on.
    pub fn hmac_algorithm(&self) -> hmac::Algorithm {
        self.0
    }

    /// The module's algorithm, or `None` for SHA-1, which it does not approve.
    #[cfg(feature = "fips")]
    fn module(&self) -> Option<&'static rind_fips::hkdf::Algorithm> {
        use digest::AlgorithmId::*;
        match self.0.digest_algorithm().id {
            SHA256 => Some(&rind_fips::hkdf::HKDF_SHA256),
            SHA384 => Some(&rind_fips::hkdf::HKDF_SHA384),
            SHA512 => Some(&rind_fips::hkdf::HKDF_SHA512),
            _ => None,
        }
    }

    fn rind(&self) -> &'static rind::hkdf::Algorithm {
        use digest::AlgorithmId::*;
        match self.0.digest_algorithm().id {
            SHA1 => &rind::hkdf::legacy::HKDF_SHA1,
            SHA256 => &rind::hkdf::HKDF_SHA256,
            SHA384 => &rind::hkdf::HKDF_SHA384,
            SHA512 => &rind::hkdf::HKDF_SHA512,
            SHA512_256 | SHA3_256 | SHA3_384 | SHA3_512 => {
                unreachable!("only this module's constants make an Algorithm")
            }
        }
    }
}

/// HKDF-SHA1, for legacy protocols only.
pub const HKDF_SHA1_FOR_LEGACY_USE_ONLY: Algorithm = Algorithm(hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY);

/// HKDF-SHA256.
pub const HKDF_SHA256: Algorithm = Algorithm(hmac::HMAC_SHA256);

/// HKDF-SHA384.
pub const HKDF_SHA384: Algorithm = Algorithm(hmac::HMAC_SHA384);

/// HKDF-SHA512.
pub const HKDF_SHA512: Algorithm = Algorithm(hmac::HMAC_SHA512);

/// An HKDF key, such as a [`Salt`] or [`Prk`], is as long as the hash's output.
impl KeyType for Algorithm {
    fn len(&self) -> usize {
        self.0.tag_len()
    }
}

/// A salt, keyed once and reused for every secret it extracts from.
pub struct Salt {
    key: hmac::Key,
    /// With `fips`, the module's salt, where the module approves extracting
    /// with it: a non-empty salt of an algorithm it offers.
    #[cfg(feature = "fips")]
    module: Option<rind_fips::hkdf::Salt>,
}

impl Salt {
    /// Keys `algorithm` with `value`; an empty `value` is RFC 5869's absent salt.
    pub fn new(algorithm: Algorithm, value: &[u8]) -> Self {
        Self {
            key: hmac::Key::new(algorithm.0, value),
            #[cfg(feature = "fips")]
            module: match algorithm.module() {
                Some(module) if !value.is_empty() => {
                    Some(rind_fips::hkdf::Salt::new(module, value))
                }
                _ => None,
            },
        }
    }

    /// RFC 5869's absent salt, as [`Salt::new`] with an empty value.
    pub fn none(algorithm: Algorithm) -> Self {
        Self::new(algorithm, &[])
    }

    /// Extracts a pseudorandom key from `secret` (HKDF-Extract).
    pub fn extract(&self, secret: &[u8]) -> Prk {
        // With `fips` and a salt the module approves, the pseudorandom key is
        // made, and stays, in the module.
        #[cfg(feature = "fips")]
        if let Some(salt) = &self.module
            && let Ok(prk) = salt.extract(secret)
        {
            return Prk {
                inner: Engine::Module(prk),
                algorithm: self.algorithm(),
                extracted: Wiped::new(true),
            };
        }
        let prk = hmac::sign(&self.key, secret);
        Prk::with_mode(self.algorithm(), prk.as_ref(), true, false)
    }

    /// The algorithm this salt was made for.
    pub fn algorithm(&self) -> Algorithm {
        Algorithm(self.key.algorithm())
    }
}

impl fmt::Debug for Salt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("hkdf::Salt")
            .field("algorithm", &self.key.algorithm())
            .finish()
    }
}

impl From<Okm<'_, Algorithm>> for Salt {
    fn from(okm: Okm<'_, Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut buffer = Wiped::new([0u8; digest::MAX_OUTPUT_LEN]);
        let value = &mut buffer[..algorithm.len()];
        okm.fill_exact(value);
        Self::new(algorithm, value)
    }
}

/// The length of what an [`Okm`] becomes.
pub trait KeyType {
    /// The length, in bytes.
    fn len(&self) -> usize;
}

/// A pseudorandom key, from which [`Prk::expand`] derives any number of keys;
/// wiped on drop.
// `extracted` records whether HKDF-Extract made it, which only `Debug` shows,
// as aws-lc-rs's does; it is wiped with the key.
#[derive(Clone)]
pub struct Prk {
    inner: Engine,
    algorithm: Algorithm,
    extracted: Wiped<bool>,
}

/// What derives from a [`Prk`]: rind, or with `fips` the module, which holds
/// the key and refuses an empty `info`, as FIPS 140-3 does not approve one.
#[derive(Clone)]
enum Engine {
    Rind(rind::hkdf::Prk),
    #[cfg(feature = "fips")]
    Module(rind_fips::hkdf::Prk),
}

impl Engine {
    /// A key in the module where `in_module` and the module offers
    /// `algorithm`; a key from an extraction the module did not approve stays
    /// in rind, whose key a caller can expand with any `info`.
    fn new(algorithm: Algorithm, value: &[u8], in_module: bool) -> Self {
        #[cfg(feature = "fips")]
        if let Some(module) = algorithm.module().filter(|_| in_module) {
            return Self::Module(rind_fips::hkdf::Prk::new(module, value));
        }
        let _ = in_module;
        Self::Rind(rind::hkdf::Prk::new(algorithm.rind(), value))
    }

    fn fill(&self, info: &[&[u8]], out: &mut [u8]) -> Result<(), error::Unspecified> {
        match self {
            Self::Rind(prk) => prk.fill(info, out).map_err(|_| error::Unspecified),
            #[cfg(feature = "fips")]
            Self::Module(prk) => prk.fill(info, out).map_err(|_| error::Unspecified),
        }
    }
}

impl Prk {
    /// Takes `value` as the pseudorandom key itself, skipping HKDF-Extract.
    pub fn new_less_safe(algorithm: Algorithm, value: &[u8]) -> Self {
        Self::with_mode(algorithm, value, false, true)
    }

    fn with_mode(algorithm: Algorithm, value: &[u8], extracted: bool, in_module: bool) -> Self {
        Self {
            inner: Engine::new(algorithm, value, in_module),
            algorithm,
            extracted: Wiped::new(extracted),
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
        // The module does not approve an empty `info`, so a key it holds
        // cannot expand one; failing here keeps `fill_exact`'s expectation.
        #[cfg(feature = "fips")]
        if matches!(self.inner, Engine::Module(_)) && info.iter().all(|part| part.is_empty()) {
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

impl fmt::Debug for Prk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("hkdf::Prk")
            .field("algorithm", &self.algorithm.0)
            .field(
                "mode",
                &format_args!(
                    "{} {{ .. }}",
                    if *self.extracted {
                        "ExtractExpand"
                    } else {
                        "Expand"
                    }
                ),
            )
            .finish()
    }
}

impl From<Okm<'_, Algorithm>> for Prk {
    fn from(okm: Okm<'_, Algorithm>) -> Self {
        let algorithm = *okm.len();
        let mut buffer = Wiped::new([0u8; digest::MAX_OUTPUT_LEN]);
        let key = &mut buffer[..algorithm.len()];
        okm.fill_exact(key);
        Self::new_less_safe(algorithm, key)
    }
}

/// Key material from [`Prk::expand`], as long as `L` says, for [`Okm::fill`] or a key's `From`.
pub struct Okm<'a, L: KeyType> {
    prk: &'a Prk,
    info: &'a [&'a [u8]],
    len: L,
    len_cached: usize,
}

impl<L: KeyType> fmt::Debug for Okm<'_, L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("hkdf::Okm").field("prk", self.prk).finish()
    }
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
        self.prk.inner.fill(self.info, out)
    }

    /// Fills `out`, which the caller made exactly the length `L` says.
    pub(crate) fn fill_exact(self, out: &mut [u8]) {
        self.fill(out)
            .expect("`expand` held the length to 255 hash outputs");
    }
}
