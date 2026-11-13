// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Hashing through an algorithm constant.

use core::fmt;

use super::hash::{
    Hash, HashContext, LegacySha1, Sha1Context, Sha256, Sha256Context, Sha384, Sha384Context,
    Sha512, Sha512Context,
};
use crate::low::{Entry, ct, ct_equal};
use crate::mid::{md5, sha1, sha2, sha3};

/// A hash function, chosen by one of this module's constants.
pub struct Algorithm {
    id: Id,
    output_len: usize,
    // The only paths to the hash's code, so a binary links only the hashes
    // whose algorithms it names.
    hash: fn(&[u8]) -> Digest,
    start: fn() -> State,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Id {
    Md5,
    Sha1,
    Sha256,
    Sha384,
    Sha512,
    Sha512_256,
    Sha3_256,
    Sha3_384,
    Sha3_512,
}

impl Algorithm {
    /// The length of this algorithm's digest, in bytes.
    pub fn output_len(&self) -> usize {
        self.output_len
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm")
            .field("id", &self.id)
            .field("output_len", &self.output_len)
            .finish()
    }
}

/// MD5, from [RFC 1321](https://www.rfc-editor.org/rfc/rfc1321), for legacy
/// protocols only: its collision resistance is broken.
///
/// Only hashing takes it: no HMAC, key derivation, or signature does.
pub static MD5: Algorithm = Algorithm {
    id: Id::Md5,
    output_len: md5::Md5Context::OUTPUT_SZ,
    hash: |data| Digest::new(&MD5, &md5::Md5State::new().finish_with(data)),
    start: Hashing::<Md5Context>::start,
};

/// SHA-1, for legacy protocols only: its collision resistance is broken.
///
/// HMAC-SHA1 does not rely on collision resistance, and remains required by
/// STUN (RFC 8489) and SRTP (RFC 3711). No signature algorithm accepts it.
pub static SHA1: Algorithm = Algorithm {
    id: Id::Sha1,
    output_len: sha1::Sha1Context::OUTPUT_SZ,
    hash: LegacySha1::hash,
    start: Hashing::<Sha1Context>::start,
};

/// SHA-256, from [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
pub static SHA256: Algorithm = Algorithm {
    id: Id::Sha256,
    output_len: sha2::Sha256Context::OUTPUT_SZ,
    hash: Sha256::hash,
    start: Hashing::<Sha256Context>::start,
};

/// SHA-384, from [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
pub static SHA384: Algorithm = Algorithm {
    id: Id::Sha384,
    output_len: sha2::Sha384Context::OUTPUT_SZ,
    hash: Sha384::hash,
    start: Hashing::<Sha384Context>::start,
};

/// SHA-512, from [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
pub static SHA512: Algorithm = Algorithm {
    id: Id::Sha512,
    output_len: sha2::Sha512Context::OUTPUT_SZ,
    hash: Sha512::hash,
    start: Hashing::<Sha512Context>::start,
};

/// SHA-512/256: SHA-512 with its own initial value, truncated to 256 bits, from [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
pub static SHA512_256: Algorithm = Algorithm {
    id: Id::Sha512_256,
    output_len: sha2::Sha512_256Context::OUTPUT_SZ,
    hash: |data| {
        let output = sha2::Sha512_256Context::INITIAL.finish_with(data);
        Digest::new(&SHA512_256, &sha2::Sha512_256Context::truncate(&output))
    },
    start: Hashing::<Sha512_256Context>::start,
};

/// SHA3-256, from [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf).
pub static SHA3_256: Algorithm = Algorithm {
    id: Id::Sha3_256,
    output_len: sha3::Sha3_256Context::OUTPUT_SZ,
    hash: one_shot::<Sha3_256Context>,
    start: Hashing::<Sha3_256Context>::start,
};

/// SHA3-384, from [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf).
pub static SHA3_384: Algorithm = Algorithm {
    id: Id::Sha3_384,
    output_len: sha3::Sha3_384Context::OUTPUT_SZ,
    hash: one_shot::<Sha3_384Context>,
    start: Hashing::<Sha3_384Context>::start,
};

/// SHA3-512, from [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf).
pub static SHA3_512: Algorithm = Algorithm {
    id: Id::Sha3_512,
    output_len: sha3::Sha3_512Context::OUTPUT_SZ,
    hash: one_shot::<Sha3_512Context>,
    start: Hashing::<Sha3_512Context>::start,
};

/// Hashes `data` in one go.
#[must_use]
pub fn digest(algorithm: &'static Algorithm, data: &[u8]) -> Digest {
    let _entry = Entry::new_secret();
    (algorithm.hash)(data)
}

/// An in-progress hash computation.
///
/// A clone forks the computation, so messages sharing a prefix hash it once.
#[derive(Clone)]
pub struct Context(State);

// `repr(u8)` lays every variant out as the tag then its `Hashing`, so `ops`
// sits at one offset in each.
#[derive(Clone)]
#[repr(u8)]
enum State {
    Md5(Hashing<Md5Context>),
    Sha1(Hashing<Sha1Context>),
    Sha256(Hashing<Sha256Context>),
    Sha384(Hashing<Sha384Context>),
    Sha512(Hashing<Sha512Context>),
    Sha512_256(Hashing<Sha512_256Context>),
    Sha3_256(Hashing<Sha3_256Context>),
    Sha3_384(Hashing<Sha3_384Context>),
    Sha3_512(Hashing<Sha3_512Context>),
}

impl State {
    fn update(&mut self, data: &[u8]) {
        match self {
            Self::Md5(hashing) => hashing.update(data),
            Self::Sha1(hashing) => hashing.update(data),
            Self::Sha256(hashing) => hashing.update(data),
            Self::Sha384(hashing) => hashing.update(data),
            Self::Sha512(hashing) => hashing.update(data),
            Self::Sha512_256(hashing) => hashing.update(data),
            Self::Sha3_256(hashing) => hashing.update(data),
            Self::Sha3_384(hashing) => hashing.update(data),
            Self::Sha3_512(hashing) => hashing.update(data),
        }
    }

    fn finish(&mut self) -> Digest {
        match self {
            Self::Md5(hashing) => hashing.finish(),
            Self::Sha1(hashing) => hashing.finish(),
            Self::Sha256(hashing) => hashing.finish(),
            Self::Sha384(hashing) => hashing.finish(),
            Self::Sha512(hashing) => hashing.finish(),
            Self::Sha512_256(hashing) => hashing.finish(),
            Self::Sha3_256(hashing) => hashing.finish(),
            Self::Sha3_384(hashing) => hashing.finish(),
            Self::Sha3_512(hashing) => hashing.finish(),
        }
    }
}

/// A hash context with its hash's code, which it reaches only through
/// `ops`: matching on [`State`] then names no hash's code.
///
/// `ops` comes first, so every variant holds it at one offset and the match
/// folds to a single load rather than a jump per variant.
#[derive(Clone)]
#[repr(C)]
struct Hashing<C: Variant> {
    ops: &'static Ops<C>,
    context: C,
}

struct Ops<C> {
    update: fn(&mut C, &[u8]),
    finish: fn(&mut C) -> Digest,
}

impl<C: Variant> Hashing<C> {
    fn start() -> State {
        C::state(Self {
            ops: const {
                &Ops {
                    update: C::update,
                    finish: C::finish_reset,
                }
            },
            context: C::NEW,
        })
    }

    fn update(&mut self, data: &[u8]) {
        (self.ops.update)(&mut self.context, data)
    }

    fn finish(&mut self) -> Digest {
        (self.ops.finish)(&mut self.context)
    }
}

/// A hash's context, as a [`State`] variant holds it.
trait Variant: HashContext + 'static {
    /// A context before any input.
    // A constant rather than a function, so starting or resetting a context
    // copies it from read-only memory instead of building it on the stack.
    const NEW: Self;

    fn state(hashing: Hashing<Self>) -> State;

    /// The digest of the message so far, leaving `self` as [`Self::NEW`].
    fn finish_reset(&mut self) -> Digest {
        let digest = self.finish();
        *self = Self::NEW;
        digest
    }
}

macro_rules! variant {
    ($context:ty, $variant:ident, $new:expr) => {
        impl Variant for $context {
            const NEW: Self = $new;

            fn state(hashing: Hashing<Self>) -> State {
                State::$variant(hashing)
            }
        }
    };
}

variant!(Sha1Context, Sha1, Sha1Context(sha1::Sha1Context::new()));
variant!(
    Sha256Context,
    Sha256,
    Sha256Context(sha2::Sha256Context::new())
);
variant!(
    Sha384Context,
    Sha384,
    Sha384Context(sha2::Sha384Context::new())
);
variant!(
    Sha512Context,
    Sha512,
    Sha512Context(sha2::Sha512Context::new())
);
variant!(
    Sha512_256Context,
    Sha512_256,
    Sha512_256Context(sha2::Sha512_256Context::new())
);

/// MD5's context, which no [`Hash`] has: nothing keyed or signed takes MD5.
#[derive(Clone)]
struct Md5Context(md5::Md5Context);

impl HashContext for Md5Context {
    fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes)
    }

    fn finish(&self) -> Digest {
        Digest::new(&MD5, &self.0.finish())
    }
}

variant!(Md5Context, Md5, Md5Context(md5::Md5Context::new()));

/// SHA-512/256's context, which no [`Hash`] has.
#[derive(Clone)]
struct Sha512_256Context(sha2::Sha512_256Context);

impl HashContext for Sha512_256Context {
    fn update(&mut self, bytes: &[u8]) {
        self.0.update(bytes)
    }

    fn finish(&self) -> Digest {
        Digest::new(&SHA512_256, &self.0.finish())
    }
}

/// A SHA-3 context, which no [`Hash`] has: HMAC and signatures take only
/// SHA-1 and SHA-2.
macro_rules! sha3_context {
    ($name:ident, $variant:ident, $algorithm:ident) => {
        #[derive(Clone)]
        struct $name(sha3::$name);

        impl HashContext for $name {
            fn update(&mut self, bytes: &[u8]) {
                self.0.update(bytes)
            }

            fn finish(&self) -> Digest {
                Digest::new(&$algorithm, &self.0.finish())
            }
        }

        variant!($name, $variant, $name(sha3::$name::new()));
    };
}

sha3_context!(Sha3_256Context, Sha3_256, SHA3_256);
sha3_context!(Sha3_384Context, Sha3_384, SHA3_384);
sha3_context!(Sha3_512Context, Sha3_512, SHA3_512);

/// Hashes `data` with a fresh `C`, for an algorithm with no [`Hash`].
fn one_shot<C: Variant>(data: &[u8]) -> Digest {
    let mut context = C::NEW;
    context.update(data);
    context.finish()
}

impl Context {
    /// Starts hashing with `algorithm`.
    pub fn new(algorithm: &'static Algorithm) -> Self {
        Self((algorithm.start)())
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        // The compressors enter instead, so an update that only buffers skips
        // the cost of enabling DIT.
        self.0.update(data);
    }

    /// Returns the digest of the message, and starts a new one with the same algorithm.
    pub fn finish(&mut self) -> Digest {
        let _entry = Entry::new_secret();
        self.0.finish()
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // An `Id`, not the static, so formatting links no hash's code.
        let algorithm = match &self.0 {
            State::Md5(_) => Id::Md5,
            State::Sha1(_) => Id::Sha1,
            State::Sha256(_) => Id::Sha256,
            State::Sha384(_) => Id::Sha384,
            State::Sha512(_) => Id::Sha512,
            State::Sha512_256(_) => Id::Sha512_256,
            State::Sha3_256(_) => Id::Sha3_256,
            State::Sha3_384(_) => Id::Sha3_384,
            State::Sha3_512(_) => Id::Sha3_512,
        };
        f.debug_struct("Context")
            .field("algorithm", &algorithm)
            .finish_non_exhaustive()
    }
}

/// The output of a hash function.
#[derive(Clone, Copy)]
pub struct Digest {
    algorithm: &'static Algorithm,
    value: [u8; MAX_OUTPUT_LEN],
}

pub(super) const MAX_OUTPUT_LEN: usize = sha2::Sha512Context::OUTPUT_SZ;

impl Digest {
    /// A digest of `algorithm` holding `value`, which must be its output length.
    pub(crate) fn new(algorithm: &'static Algorithm, value: &[u8]) -> Self {
        let mut digest = Self::zeroed(algorithm);
        digest.as_mut().copy_from_slice(value);
        digest
    }

    /// A zeroed digest of `algorithm`, for building one in place.
    pub(crate) fn zeroed(algorithm: &'static Algorithm) -> Self {
        Self {
            algorithm,
            value: [0; MAX_OUTPUT_LEN],
        }
    }

    pub(crate) fn as_mut(&mut self) -> &mut [u8] {
        &mut self.value[..self.algorithm.output_len()]
    }

    pub(super) fn id(&self) -> Id {
        self.algorithm.id
    }

    /// Constant-time equality, `other` may not be truncated.
    pub(crate) fn ct_equal(&self, other: &[u8]) -> bool {
        ct::into_public(ct_equal(self.as_ref(), other))
    }

    /// Whether a signature takes this digest: SHA-256, SHA-384, or SHA-512,
    /// as signatures over a message take.
    pub(crate) fn signs(&self) -> bool {
        matches!(self.algorithm.id, Id::Sha256 | Id::Sha384 | Id::Sha512)
    }
}

impl AsRef<[u8]> for Digest {
    fn as_ref(&self) -> &[u8] {
        &self.value[..self.algorithm.output_len()]
    }
}

impl fmt::Debug for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Digest")
            .field("algorithm", &self.algorithm.id)
            .field("value", &self.as_ref())
            .finish()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::*;

    #[test]
    fn acvp_sha256() {
        acvp_hash("SHA2-256-1.0", &SHA256);
    }

    #[test]
    fn acvp_sha384() {
        acvp_hash("SHA2-384-1.0", &SHA384);
    }

    #[test]
    fn acvp_sha512() {
        acvp_hash("SHA2-512-1.0", &SHA512);
    }

    #[test]
    fn acvp_sha512_256() {
        acvp_hash("SHA2-512-256-1.0", &SHA512_256);
    }

    #[test]
    fn acvp_sha3_256() {
        acvp_hash("SHA3-256-2.0", &SHA3_256);
    }

    #[test]
    fn acvp_sha3_384() {
        acvp_hash("SHA3-384-2.0", &SHA3_384);
    }

    #[test]
    fn acvp_sha3_512() {
        acvp_hash("SHA3-512-2.0", &SHA3_512);
    }

    /// Runs an ACVP hash set: its messages, its Monte Carlo test, and, under
    /// SLOW_TESTS, its messages of 1 to 8 GiB.
    fn acvp_hash(name: &str, algorithm: &'static Algorithm) {
        for group in acvp(name) {
            for test in group.tests() {
                let len = test.int("len") / 8;
                match group.str("testType") {
                    "AFT" => {
                        let msg = test.hex("msg");
                        assert_eq!(digest(algorithm, &msg[..len]).as_ref(), test.hex("md"));
                    }
                    "MCT" => acvp_hash_mct(algorithm, name.starts_with("SHA3"), &group, test),
                    "LDT" if std::env::var_os("SLOW_TESTS").is_some() => {
                        let large = &test["largeMsg"];
                        assert_eq!(large.str("expansionTechnique"), "repeating");
                        let content = large.hex("content");
                        let chunk = content.repeat((1 << 20) / content.len());
                        // Up to 8 GiB, more than a 32-bit `usize` holds.
                        let full_len = large["fullLength"].as_u64().unwrap() / 8;
                        let chunk_len = chunk.len() as u64;
                        assert_eq!(full_len % chunk_len, 0);
                        let mut ctx = Context::new(algorithm);
                        for _ in 0..full_len / chunk_len {
                            ctx.update(&chunk);
                        }
                        assert_eq!(ctx.finish().as_ref(), test.hex("md"));
                    }
                    "LDT" => {}
                    other => panic!("unexpected test type {other}"),
                }
            }
        }
    }

    /// The ACVP SHA specification's Monte Carlo tests: SHA-2 hashes the last
    /// three digests together, in the alternate version cut or zero-padded to
    /// the seed's length, and SHA-3 hashes the last digest alone.
    fn acvp_hash_mct(
        algorithm: &'static Algorithm,
        sha3: bool,
        group: &serde_json::Value,
        test: &serde_json::Value,
    ) {
        let seed_len = test.int("len") / 8;
        let alternate = match group.str("mctVersion") {
            "standard" => false,
            "alternate" if !sha3 => true,
            other => panic!("unexpected Monte Carlo version {other}"),
        };
        let mut seed = test.hex("msg");
        for result in test["resultsArray"].as_array().unwrap() {
            if sha3 {
                for _ in 0..1000 {
                    seed = digest(algorithm, &seed).as_ref().to_vec();
                }
            } else {
                let mut last = [seed.clone(), seed.clone(), seed];
                for _ in 0..1000 {
                    let mut msg = last.concat();
                    if alternate {
                        msg.resize(seed_len, 0);
                    }
                    last = [
                        last[1].clone(),
                        last[2].clone(),
                        digest(algorithm, &msg).as_ref().to_vec(),
                    ];
                }
                let [_, _, md] = last;
                seed = md;
            }
            assert_eq!(seed, result.hex("md"));
        }
    }

    #[test]
    fn secret_message() {
        // Under `admin/ctgrind`, nothing may branch on or index by the
        // message, which ends in a partial block of each hash.
        for algorithm in [
            &MD5,
            &SHA1,
            &SHA256,
            &SHA384,
            &SHA512,
            &SHA512_256,
            &SHA3_256,
            &SHA3_384,
            &SHA3_512,
        ] {
            let message = [0xa5; 300];
            let wanted = digest(algorithm, &message);

            ct::secret_slice(&message);
            let mut ctx = Context::new(algorithm);
            ctx.update(&message[..100]);
            ctx.update(&message[100..]);
            let got = ct::into_public(ctx.finish());
            assert_eq!(got.as_ref(), wanted.as_ref());
            let got = ct::into_public(digest(algorithm, &message));
            assert_eq!(got.as_ref(), wanted.as_ref());
        }
    }

    fn is_sha3(algorithm: &Algorithm) -> bool {
        matches!(algorithm.id, Id::Sha3_256 | Id::Sha3_384 | Id::Sha3_512)
    }

    // CAVP's `[L = n]` header gives only the output length, which SHA-256
    // and SHA-512/256 share, so each file names its algorithm. SHA-3's files
    // give it in bits, the others in bytes.
    fn check_meta(algorithm: &Algorithm, meta: &str) {
        let len = match is_sha3(algorithm) {
            true => algorithm.output_len() * 8,
            false => algorithm.output_len(),
        };
        assert_eq!(meta, format!("L = {len}"));
    }

    #[test]
    fn cavp() {
        #[derive(Debug)]
        struct Cavp {
            algorithm: &'static Algorithm,
            message: Vec<u8>,
            message_bytes: usize,
        }

        impl CavpSink for Cavp {
            fn on_meta(&mut self, meta: &str) {
                check_meta(self.algorithm, meta);
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "Len" => self.message_bytes = (value.int() / 8) as usize,
                    "Msg" => {
                        self.message = value.bytes();
                        self.message.truncate(self.message_bytes);
                    }
                    "MD" => {
                        let digest = digest(self.algorithm, &self.message);
                        assert_eq!(digest.as_ref(), value.bytes());
                    }
                    _ => todo!("{self:?} value {name} = {value:?}"),
                }
            }
        }

        for (file, algorithm) in [
            ("../thirdparty/cavp-sha1/SHA1ShortMsg.rsp", &SHA1),
            ("../thirdparty/cavp-sha1/SHA1LongMsg.rsp", &SHA1),
            ("../thirdparty/cavp/sha2/SHA256ShortMsg.rsp", &SHA256),
            ("../thirdparty/cavp/sha2/SHA256LongMsg.rsp", &SHA256),
            ("../thirdparty/cavp/sha2/SHA384ShortMsg.rsp", &SHA384),
            ("../thirdparty/cavp/sha2/SHA384LongMsg.rsp", &SHA384),
            ("../thirdparty/cavp/sha2/SHA512ShortMsg.rsp", &SHA512),
            ("../thirdparty/cavp/sha2/SHA512LongMsg.rsp", &SHA512),
            (
                "../thirdparty/cavp/sha2/SHA512_256ShortMsg.rsp",
                &SHA512_256,
            ),
            ("../thirdparty/cavp/sha2/SHA512_256LongMsg.rsp", &SHA512_256),
            ("../thirdparty/cavp/sha3/SHA3_256ShortMsg.rsp", &SHA3_256),
            ("../thirdparty/cavp/sha3/SHA3_256LongMsg.rsp", &SHA3_256),
            ("../thirdparty/cavp/sha3/SHA3_384ShortMsg.rsp", &SHA3_384),
            ("../thirdparty/cavp/sha3/SHA3_384LongMsg.rsp", &SHA3_384),
            ("../thirdparty/cavp/sha3/SHA3_512ShortMsg.rsp", &SHA3_512),
            ("../thirdparty/cavp/sha3/SHA3_512LongMsg.rsp", &SHA3_512),
        ] {
            process_cavp(
                file,
                &mut Cavp {
                    algorithm,
                    message: Vec::new(),
                    message_bytes: 0,
                },
            );
        }
    }

    // RFC 1321's test suite, as no CAVP or Wycheproof vectors cover MD5.
    #[test]
    fn rfc1321() {
        for (message, wanted) in [
            ("", "d41d8cd98f00b204e9800998ecf8427e"),
            ("a", "0cc175b9c0f1b6a831c399e269772661"),
            ("abc", "900150983cd24fb0d6963f7d28e17f72"),
            ("message digest", "f96b697d7cb7938d525a2f31aaf161d0"),
            (
                "abcdefghijklmnopqrstuvwxyz",
                "c3fcd3d76192e4007dfb496cca67e13b",
            ),
            (
                "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
                "d174ab98d277d9f5a5611c2c9f419d9f",
            ),
            (
                "12345678901234567890123456789012345678901234567890123456789012345678901234567890",
                "57edf4a22be3c955ac49da2e2107b67a",
            ),
        ] {
            let got = digest(&MD5, message.as_bytes());
            assert_eq!(got.as_ref(), hex::decode(wanted).unwrap(), "{message:?}");
        }
    }

    // `finish` leaves a fresh context: each message after it hashes alone,
    // whether a partial block, several blocks, or nothing was left buffered.
    #[test]
    fn finish_resets() {
        for algorithm in [
            &MD5,
            &SHA1,
            &SHA256,
            &SHA384,
            &SHA512,
            &SHA512_256,
            &SHA3_256,
            &SHA3_384,
            &SHA3_512,
        ] {
            let mut ctx = Context::new(algorithm);
            for message in [&[0x61u8; 3][..], &[0x62; 300], &[], &[0x63; 128]] {
                ctx.update(message);
                assert_eq!(
                    ctx.finish().as_ref(),
                    digest(algorithm, message).as_ref(),
                    "{algorithm:?}, {} bytes",
                    message.len()
                );
            }
        }
    }

    #[test]
    fn cavp_monte_carlo() {
        #[derive(Debug)]
        struct Cavp {
            algorithm: &'static Algorithm,
            seed: Vec<u8>,
        }

        impl CavpSink for Cavp {
            fn on_meta(&mut self, meta: &str) {
                check_meta(self.algorithm, meta);
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "Seed" => self.seed = value.bytes(),
                    "COUNT" => {}
                    "MD" => {
                        self.seed = match is_sha3(self.algorithm) {
                            true => sha3_monte_carlo_1000(self.algorithm, &self.seed),
                            false => monte_carlo_1000(self.algorithm, &self.seed),
                        };
                        assert_eq!(self.seed, value.bytes());
                    }
                    _ => todo!("{self:?} value {name} = {value:?}"),
                }
            }
        }

        fn monte_carlo_1000(algorithm: &'static Algorithm, seed: &[u8]) -> Vec<u8> {
            let mut window = [seed.to_vec(), seed.to_vec(), seed.to_vec()];
            for _ in 0..1000 {
                let mut ctx = Context::new(algorithm);
                ctx.update(&window[0]);
                ctx.update(&window[1]);
                ctx.update(&window[2]);
                let r = ctx.finish();
                window.rotate_left(1);
                window[2].copy_from_slice(r.as_ref());
            }
            window[2].clone()
        }

        // SHA3VS hashes each digest alone, rather than the last three.
        fn sha3_monte_carlo_1000(algorithm: &'static Algorithm, seed: &[u8]) -> Vec<u8> {
            let mut md = seed.to_vec();
            for _ in 0..1000 {
                md = digest(algorithm, &md).as_ref().to_vec();
            }
            md
        }

        if std::env::var_os("SLOW_TESTS").is_some() {
            for (file, algorithm) in [
                ("../thirdparty/cavp-sha1/SHA1Monte.rsp", &SHA1),
                ("../thirdparty/cavp/sha2/SHA256Monte.rsp", &SHA256),
                ("../thirdparty/cavp/sha2/SHA384Monte.rsp", &SHA384),
                ("../thirdparty/cavp/sha2/SHA512Monte.rsp", &SHA512),
                ("../thirdparty/cavp/sha2/SHA512_256Monte.rsp", &SHA512_256),
                ("../thirdparty/cavp/sha3/SHA3_256Monte.rsp", &SHA3_256),
                ("../thirdparty/cavp/sha3/SHA3_384Monte.rsp", &SHA3_384),
                ("../thirdparty/cavp/sha3/SHA3_512Monte.rsp", &SHA3_512),
            ] {
                process_cavp(
                    file,
                    &mut Cavp {
                        algorithm,
                        seed: Vec::new(),
                    },
                );
            }
        }
    }
}
