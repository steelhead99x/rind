//! Cryptographic hash functions.
//!
//! aws-lc-rs's SHA-224 is not offered: rind lacks it. Nor is
//! `Digest::import_less_safe`: rind signs and verifies only digests it
//! computed.

use core::fmt;

/// A hash function, chosen by one of this module's constants.
pub struct Algorithm {
    /// The length of a digest, in bytes.
    pub output_len: usize,

    /// The length of the hash's internal state, in bytes, which aws-lc-rs
    /// keeps only for ring compatibility.
    #[deprecated(
        since = "1.1.0",
        note = "Unused by aws-lc-rs; retained for ring compatibility. Use `output_len()` to size an HMAC key."
    )]
    pub chaining_len: usize,

    /// The length of a block the hash compresses at a time, in bytes.
    pub block_len: usize,

    pub(crate) id: AlgorithmId,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AlgorithmId {
    SHA1,
    SHA256,
    SHA384,
    SHA512,
    SHA512_256,
    SHA3_256,
    SHA3_384,
    SHA3_512,
}

impl Algorithm {
    /// The length of a digest, in bytes.
    pub fn output_len(&self) -> usize {
        self.output_len
    }

    /// The length of the hash's internal state, in bytes.
    #[deprecated(
        since = "1.1.0",
        note = "Unused by aws-lc-rs; retained for ring compatibility. Use `output_len()` to size an HMAC key."
    )]
    pub fn chaining_len(&self) -> usize {
        #[allow(deprecated)]
        self.chaining_len
    }

    /// The length of a block the hash compresses at a time, in bytes.
    pub fn block_len(&self) -> usize {
        self.block_len
    }

    /// With `fips`, the module's algorithm, where it approves the hash: all
    /// but SHA-1, which stays in rind as in aws-lc-rs's FIPS build.
    #[cfg(feature = "fips")]
    fn module(&self) -> Option<&'static rind_fips::digest::Algorithm> {
        Some(match self.id {
            AlgorithmId::SHA1 => return None,
            AlgorithmId::SHA256 => &rind_fips::digest::SHA256,
            AlgorithmId::SHA384 => &rind_fips::digest::SHA384,
            AlgorithmId::SHA512 => &rind_fips::digest::SHA512,
            AlgorithmId::SHA512_256 => &rind_fips::digest::SHA512_256,
            AlgorithmId::SHA3_256 => &rind_fips::digest::SHA3_256,
            AlgorithmId::SHA3_384 => &rind_fips::digest::SHA3_384,
            AlgorithmId::SHA3_512 => &rind_fips::digest::SHA3_512,
        })
    }

    pub(crate) fn rind(&self) -> &'static rind::digest::Algorithm {
        match self.id {
            AlgorithmId::SHA1 => &rind::digest::legacy::SHA1,
            AlgorithmId::SHA256 => &rind::digest::SHA256,
            AlgorithmId::SHA384 => &rind::digest::SHA384,
            AlgorithmId::SHA512 => &rind::digest::SHA512,
            AlgorithmId::SHA512_256 => &rind::digest::SHA512_256,
            AlgorithmId::SHA3_256 => &rind::digest::SHA3_256,
            AlgorithmId::SHA3_384 => &rind::digest::SHA3_384,
            AlgorithmId::SHA3_512 => &rind::digest::SHA3_512,
        }
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Algorithm {}

macro_rules! algorithm {
    ($name:ident, $id:ident, $output_len:expr, $chaining_len:expr, $block_len:expr, $doc:expr) => {
        #[doc = $doc]
        #[allow(deprecated)]
        pub const $name: Algorithm = Algorithm {
            output_len: $output_len,
            chaining_len: $chaining_len,
            block_len: $block_len,
            id: AlgorithmId::$id,
        };
    };
}

algorithm!(
    SHA1_FOR_LEGACY_USE_ONLY,
    SHA1,
    SHA1_OUTPUT_LEN,
    SHA1_OUTPUT_LEN,
    64,
    "SHA-1, for legacy protocols only: its collision resistance is broken."
);
algorithm!(
    SHA256,
    SHA256,
    SHA256_OUTPUT_LEN,
    SHA256_OUTPUT_LEN,
    64,
    "SHA-256."
);
algorithm!(
    SHA384,
    SHA384,
    SHA384_OUTPUT_LEN,
    SHA512_OUTPUT_LEN,
    128,
    "SHA-384."
);
algorithm!(
    SHA512,
    SHA512,
    SHA512_OUTPUT_LEN,
    SHA512_OUTPUT_LEN,
    128,
    "SHA-512."
);
algorithm!(
    SHA512_256,
    SHA512_256,
    SHA512_256_OUTPUT_LEN,
    SHA512_OUTPUT_LEN,
    128,
    "SHA-512/256."
);
algorithm!(SHA3_256, SHA3_256, 32, 32, 136, "SHA3-256.");
algorithm!(SHA3_384, SHA3_384, 48, 48, 104, "SHA3-384.");
algorithm!(SHA3_512, SHA3_512, 64, 64, 72, "SHA3-512.");

/// The largest block length of any algorithm, in bytes.
pub const MAX_BLOCK_LEN: usize = 128;

/// The largest digest length of any algorithm, in bytes.
pub const MAX_OUTPUT_LEN: usize = 64;

/// The largest internal state of any algorithm, in bytes.
pub const MAX_CHAINING_LEN: usize = MAX_OUTPUT_LEN;

/// The length of a SHA-1 digest, in bytes.
pub const SHA1_OUTPUT_LEN: usize = 20;

/// The length of a SHA-256 digest, in bytes.
pub const SHA256_OUTPUT_LEN: usize = 32;

/// The length of a SHA-384 digest, in bytes.
pub const SHA384_OUTPUT_LEN: usize = 48;

/// The length of a SHA-512 digest, in bytes.
pub const SHA512_OUTPUT_LEN: usize = 64;

/// The length of a SHA-512/256 digest, in bytes.
pub const SHA512_256_OUTPUT_LEN: usize = 32;

/// Hashes `data` in one go.
pub fn digest(algorithm: &'static Algorithm, data: &[u8]) -> Digest {
    let mut ctx = Context::new(algorithm);
    ctx.update(data);
    ctx.finish()
}

/// An in-progress hash computation; a clone forks it.
#[derive(Clone)]
pub struct Context {
    inner: ContextInner,
    algorithm: &'static Algorithm,
}

/// Where a hash runs: rind, or with `fips` the module for every hash it
/// approves.
#[derive(Clone)]
#[allow(
    clippy::large_enum_variant,
    reason = "a context is a value, as rind's is"
)]
enum ContextInner {
    Rind(rind::digest::Context),
    #[cfg(feature = "fips")]
    Module(rind_fips::digest::Context),
}

impl Context {
    /// Starts hashing with `algorithm`.
    pub fn new(algorithm: &'static Algorithm) -> Self {
        #[cfg(feature = "fips")]
        if let Some(module) = algorithm.module() {
            return Self {
                inner: ContextInner::Module(rind_fips::digest::Context::new(module)),
                algorithm,
            };
        }
        Self {
            inner: ContextInner::Rind(rind::digest::Context::new(algorithm.rind())),
            algorithm,
        }
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        match &mut self.inner {
            ContextInner::Rind(inner) => inner.update(data),
            #[cfg(feature = "fips")]
            ContextInner::Module(inner) => inner.update(data),
        }
    }

    /// Returns the digest of the message.
    pub fn finish(mut self) -> Digest {
        let inner = match &mut self.inner {
            ContextInner::Rind(inner) => DigestInner::Rind(inner.finish()),
            #[cfg(feature = "fips")]
            ContextInner::Module(inner) => DigestInner::Module(inner.finish()),
        };
        Digest {
            inner,
            algorithm: self.algorithm,
        }
    }

    /// The algorithm this context hashes with.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }
}

/// The output of a hash function.
#[derive(Clone, Copy)]
pub struct Digest {
    inner: DigestInner,
    algorithm: &'static Algorithm,
}

#[derive(Clone, Copy)]
#[allow(
    clippy::large_enum_variant,
    reason = "a digest is a value, copied whole"
)]
enum DigestInner {
    Rind(rind::digest::Digest),
    #[cfg(feature = "fips")]
    Module(rind_fips::digest::Digest),
}

impl Digest {
    /// The algorithm that made this digest.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// The digest as the backend that signs it holds it: the module's under
    /// `fips`, which signs only the hashes it approves, so a SHA-1 digest
    /// is `None`; rind's otherwise.
    #[cfg(feature = "fips")]
    pub(crate) fn signing(&self) -> Option<&rind_fips::digest::Digest> {
        match &self.inner {
            DigestInner::Module(inner) => Some(inner),
            DigestInner::Rind(_) => None,
        }
    }

    #[cfg(not(feature = "fips"))]
    pub(crate) fn signing(&self) -> Option<&rind::digest::Digest> {
        match &self.inner {
            DigestInner::Rind(inner) => Some(inner),
        }
    }
}

impl AsRef<[u8]> for Digest {
    fn as_ref(&self) -> &[u8] {
        match &self.inner {
            DigestInner::Rind(inner) => inner.as_ref(),
            #[cfg(feature = "fips")]
            DigestInner::Module(inner) => inner.as_ref(),
        }
    }
}

impl fmt::Debug for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}:", self.algorithm)?;
        crate::write_hex(f, self.as_ref())
    }
}

/// With `fips`, the module hashes all but SHA-1, which it does not approve.
#[cfg(all(test, feature = "fips"))]
mod fips_tests {
    use super::*;

    #[test]
    fn the_module_hashes_what_it_approves() {
        for algorithm in [
            &SHA256,
            &SHA384,
            &SHA512,
            &SHA512_256,
            &SHA3_256,
            &SHA3_384,
            &SHA3_512,
        ] {
            let digest = digest(algorithm, b"abc");
            assert!(
                matches!(digest.inner, DigestInner::Module(_)),
                "{algorithm:?}"
            );
            assert!(digest.signing().is_some());
        }
        let digest = digest(&SHA1_FOR_LEGACY_USE_ONLY, b"abc");
        assert!(matches!(digest.inner, DigestInner::Rind(_)));
        assert!(digest.signing().is_none());
    }

    #[test]
    fn a_fork_of_the_module_context_hashes_alike() {
        let mut context = Context::new(&SHA256);
        context.update(b"a");
        let mut fork = context.clone();
        context.update(b"bc");
        fork.update(b"bc");
        assert_eq!(context.finish().as_ref(), fork.finish().as_ref());
    }
}
