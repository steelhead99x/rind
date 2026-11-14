// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::ops::{Deref, DerefMut};

use super::digest::{Algorithm, Digest, SHA1, SHA256, SHA384, SHA512};
use crate::low::UpdateBlocks;
use crate::mid::{sha1, sha2};

/// One block of hash function input.
#[derive(Copy, Clone)]
pub(crate) struct HashBlock {
    buf: [u8; 128],
    len: usize,
}

impl HashBlock {
    /// Creates a new `HashBlock`, containing `len` zeroed bytes.
    fn new(len: usize) -> Self {
        Self {
            buf: [0u8; 128],
            len,
        }
    }
}

impl Deref for HashBlock {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        &self.buf[..self.len]
    }
}

impl DerefMut for HashBlock {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buf[..self.len]
    }
}

/// A generic trait over supported hash functions.
///
/// This exists so (eg.) HMAC may be generic. It is not exported: callers
/// hash through [`crate::digest`] and name a hash by its algorithm constant.
pub(crate) trait Hash {
    /// The associated context type.
    type Context: HashContext;

    /// The associated chaining value type.
    type State: HashState<Context = Self::Context>;

    /// This hash function's [`crate::digest`] constant.
    const ALGORITHM: &'static Algorithm;

    /// The chaining value before any input.
    fn initial() -> Self::State;

    /// Create a new hash context.
    fn new() -> Self::Context;

    /// Hash the given bytes (one-shot style) and return the output.
    fn hash(bytes: &[u8]) -> Digest {
        Self::initial().finish_with(bytes)
    }

    /// Return a zeroed `HashBlock` of the correct size.
    fn zeroed_block() -> HashBlock;

    /// Return a zeroed [`Digest`] of the correct size.
    fn zeroed_output() -> Digest {
        Digest::zeroed(Self::ALGORITHM)
    }
}

/// A [`Hash`] whose collision resistance holds, so signatures may use it.
///
/// This excludes [`LegacySha1`].
pub(crate) trait SignatureHash: Hash {}

/// A generic trait over supported hash function contexts.
///
/// These may be cloned: the semantics of that forks the
/// computation so two different messages with the same
/// prefix can be computed, without reprocessing the prefix.
/// This property is essential to efficiently compute HMAC
/// when used for PBKDF2.
///
/// Implemented on newtypes here rather than on the `mid` contexts:
/// `admin/structure` names a trait impl's methods by the type's path, so
/// an impl on a `mid` type returning [`Digest`] reads as `mid` using `high`.
pub(crate) trait HashContext: Clone {
    /// Hash the given `bytes`.
    fn update(&mut self, bytes: &[u8]);

    /// Complete the computation.
    fn finish(&self) -> Digest;
}

/// A generic trait over a hash function's chaining value after whole blocks.
///
/// HMAC keeps one for each of its keyed hashes, and finishes a message from
/// it without a context's buffer.
pub(crate) trait HashState: Clone {
    /// The context that continues from this state.
    type Context;

    /// Hash `blocks`, a whole number of blocks.
    fn update_blocks(&mut self, blocks: &[u8]);

    /// The digest of the input so far followed by `message`, leaving this state as it was.
    fn finish_with(&self, message: &[u8]) -> Digest;

    /// A context continuing from this state.
    fn resume(&self) -> Self::Context;
}

/// SHA-1, for legacy protocols only.
///
/// SHA1 is standardized in [FIPS180](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
/// Its collision resistance is broken, so no signature accepts it.
/// HMAC-SHA1 does not rely on collision resistance, and remains
/// required by STUN (RFC 8489) and SRTP (RFC 3711).
#[derive(Clone)]
pub(crate) struct LegacySha1;

impl Hash for LegacySha1 {
    type Context = Sha1Context;
    type State = Sha1State;
    const ALGORITHM: &'static Algorithm = &SHA1;

    fn new() -> Self::Context {
        Sha1Context(sha1::Sha1Context::new())
    }

    fn initial() -> Self::State {
        Sha1State(sha1::Sha1State::new())
    }

    fn zeroed_block() -> HashBlock {
        HashBlock::new(sha1::Sha1Context::BLOCK_SZ)
    }
}

#[derive(Clone)]
pub(crate) struct Sha1Context(pub(super) sha1::Sha1Context);

impl HashContext for Sha1Context {
    fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes)
    }

    fn finish(&self) -> Digest {
        Digest::new(LegacySha1::ALGORITHM, &self.0.finish())
    }
}

#[derive(Clone)]
pub(crate) struct Sha1State(sha1::Sha1State);

impl HashState for Sha1State {
    type Context = Sha1Context;

    fn update_blocks(&mut self, blocks: &[u8]) {
        self.0.update_blocks(blocks)
    }

    fn finish_with(&self, message: &[u8]) -> Digest {
        Digest::new(LegacySha1::ALGORITHM, &self.0.finish_with(message))
    }

    fn resume(&self) -> Self::Context {
        Sha1Context(sha1::Sha1Context::resume(self.0.clone()))
    }
}

/// SHA-256.
///
/// SHA256 is standardized in [FIPS180](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
#[derive(Clone)]
pub(crate) struct Sha256;

impl Hash for Sha256 {
    type Context = Sha256Context;
    type State = Sha256State;
    const ALGORITHM: &'static Algorithm = &SHA256;

    fn new() -> Self::Context {
        Sha256Context(sha2::Sha256Context::new())
    }

    fn initial() -> Self::State {
        Sha256State(sha2::Sha256State::new())
    }

    fn zeroed_block() -> HashBlock {
        HashBlock::new(sha2::Sha256Context::BLOCK_SZ)
    }
}

impl SignatureHash for Sha256 {}

#[derive(Clone)]
pub(crate) struct Sha256Context(pub(super) sha2::Sha256Context);

impl HashContext for Sha256Context {
    fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes)
    }

    fn finish(&self) -> Digest {
        Digest::new(Sha256::ALGORITHM, &self.0.finish())
    }
}

#[derive(Clone)]
pub(crate) struct Sha256State(sha2::Sha256State);

impl HashState for Sha256State {
    type Context = Sha256Context;

    fn update_blocks(&mut self, blocks: &[u8]) {
        self.0.update_blocks(blocks)
    }

    fn finish_with(&self, message: &[u8]) -> Digest {
        Digest::new(Sha256::ALGORITHM, &self.0.finish_with(message))
    }

    fn resume(&self) -> Self::Context {
        Sha256Context(sha2::Sha256Context::resume(self.0.clone()))
    }
}

/// SHA-384.
///
/// SHA384 is standardized in [FIPS180](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
#[derive(Clone)]
pub(crate) struct Sha384;

impl Hash for Sha384 {
    type Context = Sha384Context;
    type State = Sha384State;
    const ALGORITHM: &'static Algorithm = &SHA384;

    fn new() -> Self::Context {
        Sha384Context(sha2::Sha384Context::new())
    }

    fn initial() -> Self::State {
        Sha384State(sha2::Sha384Context::INITIAL)
    }

    fn zeroed_block() -> HashBlock {
        HashBlock::new(sha2::Sha512Context::BLOCK_SZ)
    }
}

impl SignatureHash for Sha384 {}

#[derive(Clone)]
pub(crate) struct Sha384Context(pub(super) sha2::Sha384Context);

impl HashContext for Sha384Context {
    fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes)
    }

    fn finish(&self) -> Digest {
        Digest::new(Sha384::ALGORITHM, &self.0.finish())
    }
}

#[derive(Clone)]
pub(crate) struct Sha384State(sha2::Sha512State);

impl HashState for Sha384State {
    type Context = Sha384Context;

    fn update_blocks(&mut self, blocks: &[u8]) {
        self.0.update_blocks(blocks)
    }

    fn finish_with(&self, message: &[u8]) -> Digest {
        Digest::new(
            Sha384::ALGORITHM,
            &sha2::Sha384Context::truncate(&self.0.finish_with(message)),
        )
    }

    fn resume(&self) -> Self::Context {
        Sha384Context(sha2::Sha384Context::resume(self.0.clone()))
    }
}

/// SHA-512.
///
/// SHA512 is standardized in [FIPS180](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
#[derive(Clone)]
pub(crate) struct Sha512;

impl Hash for Sha512 {
    type Context = Sha512Context;
    type State = Sha512State;
    const ALGORITHM: &'static Algorithm = &SHA512;

    fn new() -> Self::Context {
        Sha512Context(sha2::Sha512Context::new())
    }

    fn initial() -> Self::State {
        Sha512State(sha2::Sha512State::new())
    }

    fn zeroed_block() -> HashBlock {
        HashBlock::new(sha2::Sha512Context::BLOCK_SZ)
    }
}

impl SignatureHash for Sha512 {}

#[derive(Clone)]
pub(crate) struct Sha512Context(pub(super) sha2::Sha512Context);

impl HashContext for Sha512Context {
    fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes)
    }

    fn finish(&self) -> Digest {
        Digest::new(Sha512::ALGORITHM, &self.0.finish())
    }
}

#[derive(Clone)]
pub(crate) struct Sha512State(sha2::Sha512State);

impl HashState for Sha512State {
    type Context = Sha512Context;

    fn update_blocks(&mut self, blocks: &[u8]) {
        self.0.update_blocks(blocks)
    }

    fn finish_with(&self, message: &[u8]) -> Digest {
        Digest::new(Sha512::ALGORITHM, &self.0.finish_with(message))
    }

    fn resume(&self) -> Self::Context {
        Sha512Context(sha2::Sha512Context::resume(self.0.clone()))
    }
}
