// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! HMAC (Hash Message Authentication Code).
//!
//! HMAC is standardized in [FIPS 198](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.198-1.pdf).

use core::fmt;

use super::digest::Digest;
use super::hash::{Hash, HashContext, HashState, LegacySha1, Sha256, Sha384, Sha512};
use crate::Error;
use crate::low::{Entry, Zeroable, ZeroableRef, zeroise_value};
use crate::mid::{sha1, sha2};

/// HMAC's keyed hash states, each one key block in, using hash function `H`.
pub(crate) struct HmacKey<H: Hash> {
    inner: H::State,
    outer: H::State,
}

// Not derived: that would also require `H: Clone`, which code generic over `H: Hash` cannot assume.
impl<H: Hash> Clone for HmacKey<H> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            outer: self.outer.clone(),
        }
    }
}

impl<H: Hash> HmacKey<H> {
    /// Keys HMAC with `key`, which may be any length.
    pub(crate) fn new(key: &[u8]) -> Self {
        let mut key_block = H::zeroed_block();

        // shorten long keys
        if key.len() > key_block.len() {
            let h_key = H::hash(key);
            key_block[..h_key.as_ref().len()].copy_from_slice(h_key.as_ref());
        } else {
            key_block[..key.len()].copy_from_slice(key);
        }

        // compute inner
        for byte in key_block.iter_mut() {
            *byte ^= 0x36;
        }
        let mut inner = H::initial();
        inner.update_blocks(&key_block);

        // and outer
        for byte in key_block.iter_mut() {
            *byte ^= 0x5c ^ 0x36;
        }
        let mut outer = H::initial();
        outer.update_blocks(&key_block);

        Self { inner, outer }
    }

    /// The tag of `message`, finished straight from the keyed states.
    pub(crate) fn sign(&self, message: &[u8]) -> Digest {
        let inner = self.inner.finish_with(message);
        self.outer.finish_with(inner.as_ref())
    }

    /// Starts a tag computation for a message given in pieces.
    pub(crate) fn start(&self) -> Hmac<H> {
        Hmac {
            inner: self.inner.resume(),
            outer: self.outer.clone(),
        }
    }
}

/// An in-progress HMAC computation, using hash function `H`.
pub(crate) struct Hmac<H: Hash> {
    inner: H::Context,
    outer: H::State,
}

// Not derived, as for `HmacKey`.
impl<H: Hash> Clone for Hmac<H> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            outer: self.outer.clone(),
        }
    }
}

impl<H: Hash> Hmac<H> {
    /// Add data to be signed.
    pub(crate) fn update(&mut self, bytes: impl AsRef<[u8]>) {
        self.inner.update(bytes.as_ref());
    }

    /// Complete the HMAC signing operation.
    ///
    /// The HMAC output (sometimes called a "signature", or "tag") is returned.
    pub(crate) fn finish(&self) -> Digest {
        let inner = self.inner.finish();
        self.outer.finish_with(inner.as_ref())
    }
}

/// An HMAC algorithm, chosen by one of this module's constants.
pub struct Algorithm {
    id: Id,
    tag_len: usize,
    // The only path to the hash's code, so a binary links only the hashes
    // whose algorithms it names.
    key: fn(&[u8]) -> Keyed,
}

// Only the digests HMAC offers, so a key is made for every value.
#[derive(Clone, Copy, Debug)]
pub(super) enum Id {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

impl Algorithm {
    /// The length of this algorithm's tag, in bytes.
    pub fn tag_len(&self) -> usize {
        self.tag_len
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Algorithm").field(&self.id).finish()
    }
}

/// HMAC-SHA1, for legacy protocols only.
///
/// HMAC does not rely on SHA-1's broken collision resistance, and STUN
/// (RFC 8489) and SRTP (RFC 3711) still require it.
pub static HMAC_SHA1: Algorithm = Algorithm {
    id: Id::Sha1,
    tag_len: sha1::Sha1Context::OUTPUT_SZ,
    key: Keying::<LegacySha1>::with_key,
};

/// HMAC-SHA256.
pub static HMAC_SHA256: Algorithm = Algorithm {
    id: Id::Sha256,
    tag_len: sha2::Sha256Context::OUTPUT_SZ,
    key: Keying::<Sha256>::with_key,
};

/// HMAC-SHA384.
pub static HMAC_SHA384: Algorithm = Algorithm {
    id: Id::Sha384,
    tag_len: sha2::Sha384Context::OUTPUT_SZ,
    key: Keying::<Sha384>::with_key,
};

/// HMAC-SHA512.
pub static HMAC_SHA512: Algorithm = Algorithm {
    id: Id::Sha512,
    tag_len: sha2::Sha512Context::OUTPUT_SZ,
    key: Keying::<Sha512>::with_key,
};

/// An HMAC key, keyed once and reused for every message; wiped on drop under the `wipe` feature.
#[derive(Clone)]
pub struct Key(Keyed);

impl Key {
    /// Keys `algorithm` with `key_value`, which may be any length.
    pub fn new(algorithm: &'static Algorithm, key_value: &[u8]) -> Self {
        let _entry = Entry::new_secret();
        Self((algorithm.key)(key_value))
    }

    /// The tag of `data`, for callers that have entered.
    // Out of line: inlined into PBKDF2's loop, LLVM unswitches the loop on
    // the largest variant's `ops`, which a smaller key leaves uninitialized,
    // so memcheck reports a branch on undefined bytes. The cost is one call
    // beside each HMAC's two compressions.
    #[inline(never)]
    pub(super) fn tag(&self, data: &[u8]) -> Digest {
        self.0.sign(data)
    }

    /// Starts a tag computation, for callers that will not keep it.
    pub(super) fn start(&self) -> Streaming {
        self.0.start()
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        match &self.0 {
            Keyed::Sha1(key) => key.ops.get().algorithm,
            Keyed::Sha256(key) => key.ops.get().algorithm,
            Keyed::Sha384(key) => key.ops.get().algorithm,
            Keyed::Sha512(key) => key.ops.get().algorithm,
        }
    }

    /// The hash this key was made for, which the `Debug` of every key built
    /// on HMAC shows.
    pub(super) fn id(&self) -> Id {
        self.algorithm().id
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("algorithm", &self.id())
            .finish_non_exhaustive()
    }
}

/// An in-progress tag computation, for a message given in pieces; wiped on drop under the `wipe` feature.
///
/// A clone forks the computation, so messages sharing a prefix process it once.
#[derive(Clone)]
pub struct Context(Streaming);

impl Context {
    /// Starts a tag computation under `key`.
    pub fn with_key(key: &Key) -> Self {
        Self(key.0.start())
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }

    /// Returns the tag of the message.
    #[must_use]
    pub fn sign(self) -> Tag {
        let _entry = Entry::new_secret();
        Tag(self.0.finish())
    }
}

// The caller holds this keyed state for as long as it likes, so it wipes as
// a key does. `Streaming` itself does not, for HKDF's and PBKDF2's copies
// inside a call.
impl Drop for Context {
    fn drop(&mut self) {
        zeroise_value(&mut self.0);
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // An `Id`, not the static, so formatting links no other hash's code.
        let algorithm = match &self.0.0 {
            Tagged::Sha1(_) => Id::Sha1,
            Tagged::Sha256(_) => Id::Sha256,
            Tagged::Sha384(_) => Id::Sha384,
            Tagged::Sha512(_) => Id::Sha512,
        };
        f.debug_struct("Context")
            .field("algorithm", &algorithm)
            .finish_non_exhaustive()
    }
}

/// Returns the tag of `data` under `key`.
#[must_use]
pub fn sign(key: &Key, data: &[u8]) -> Tag {
    let _entry = Entry::new_secret();
    Tag(key.0.sign(data))
}

/// Checks in constant time that `tag` is the whole tag of `data` under `key`.
///
/// Fails with [`Error::BadSignature`] otherwise, including for a truncated tag.
/// To check a tag over a message fed in pieces, or one truncated to a length
/// the protocol fixes (SRTP's HMAC-SHA1-80), sign with a [`Context`] or
/// [`sign`] and compare the agreed prefix with [`crate::constant_time::verify`].
pub fn verify(key: &Key, data: &[u8], tag: &[u8]) -> Result<(), Error> {
    let _entry = Entry::new_secret();
    match key.0.sign(data).ct_equal(tag) {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

/// An HMAC tag.
#[derive(Clone)]
pub struct Tag(Digest);

// The bytes stay out: a tag is secret where HMAC serves as a PRF.
impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tag")
            .field("algorithm", &self.0.id())
            .finish_non_exhaustive()
    }
}

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

// All-zero is the `Sha1` variant with all-zero hash states and a `None`
// `ZeroableRef`, which `Zeroable` allows: every other field is a plain integer
// or byte array.
#[derive(Clone)]
#[repr(u8)]
enum Keyed {
    Sha1(Keying<LegacySha1>),
    Sha256(Keying<Sha256>),
    Sha384(Keying<Sha384>),
    Sha512(Keying<Sha512>),
}

impl Keyed {
    fn sign(&self, data: &[u8]) -> Digest {
        match self {
            Self::Sha1(key) => key.sign(data),
            Self::Sha256(key) => key.sign(data),
            Self::Sha384(key) => key.sign(data),
            Self::Sha512(key) => key.sign(data),
        }
    }

    fn start(&self) -> Streaming {
        Streaming(match self {
            Self::Sha1(key) => key.start(),
            Self::Sha256(key) => key.start(),
            Self::Sha384(key) => key.start(),
            Self::Sha512(key) => key.start(),
        })
    }
}

impl Drop for Keyed {
    fn drop(&mut self) {
        // Wipes the keyed hash states, the discriminant, and the space a
        // smaller variant leaves unused.
        zeroise_value(self);
    }
}

impl Zeroable for Keyed {}

/// An in-progress tag computation that, unlike a [`Context`], is not wiped on drop.
#[derive(Clone)]
pub(super) struct Streaming(Tagged);

// As `Keyed`, with all-zero hash contexts too.
#[derive(Clone)]
#[repr(u8)]
enum Tagged {
    Sha1(Tagging<LegacySha1>),
    Sha256(Tagging<Sha256>),
    Sha384(Tagging<Sha384>),
    Sha512(Tagging<Sha512>),
}

impl Streaming {
    pub(super) fn update(&mut self, data: &[u8]) {
        // The compressors enter instead, so an update that only buffers skips
        // the cost of enabling DIT.
        match &mut self.0 {
            Tagged::Sha1(hmac) => hmac.update(data),
            Tagged::Sha256(hmac) => hmac.update(data),
            Tagged::Sha384(hmac) => hmac.update(data),
            Tagged::Sha512(hmac) => hmac.update(data),
        }
    }

    /// The tag of the message so far, for callers that have entered.
    pub(super) fn finish(&self) -> Digest {
        match &self.0 {
            Tagged::Sha1(hmac) => hmac.finish(),
            Tagged::Sha256(hmac) => hmac.finish(),
            Tagged::Sha384(hmac) => hmac.finish(),
            Tagged::Sha512(hmac) => hmac.finish(),
        }
    }
}

impl Zeroable for Streaming {}

/// A hash HMAC offers, and its places in [`Keyed`] and [`Tagged`].
trait HmacHash: Hash + Sized + 'static {
    const HMAC: &'static Algorithm;

    fn keyed(key: Keying<Self>) -> Keyed;

    fn tagged(hmac: Tagging<Self>) -> Tagged;
}

macro_rules! hmac_hash {
    ($hash:ident, $variant:ident, $algorithm:ident) => {
        impl HmacHash for $hash {
            const HMAC: &'static Algorithm = &$algorithm;

            fn keyed(key: Keying<Self>) -> Keyed {
                Keyed::$variant(key)
            }

            fn tagged(hmac: Tagging<Self>) -> Tagged {
                Tagged::$variant(hmac)
            }
        }
    };
}

hmac_hash!(LegacySha1, Sha1, HMAC_SHA1);
hmac_hash!(Sha256, Sha256, HMAC_SHA256);
hmac_hash!(Sha384, Sha384, HMAC_SHA384);
hmac_hash!(Sha512, Sha512, HMAC_SHA512);

/// A key with its hash's code, which it reaches only through `ops`:
/// matching on [`Keyed`] then names no hash's code.
struct Keying<H: HmacHash> {
    key: HmacKey<H>,
    ops: ZeroableRef<KeyOps<H>>,
}

struct KeyOps<H: HmacHash> {
    algorithm: &'static Algorithm,
    sign: fn(&HmacKey<H>, &[u8]) -> Digest,
    start: fn(&HmacKey<H>) -> Tagged,
}

// Not derived, as for `HmacKey`.
impl<H: HmacHash> Clone for Keying<H> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            ops: self.ops,
        }
    }
}

impl<H: HmacHash> Keying<H> {
    fn with_key(key: &[u8]) -> Keyed {
        H::keyed(Self {
            key: HmacKey::new(key),
            ops: ZeroableRef::new(
                const {
                    &KeyOps {
                        algorithm: H::HMAC,
                        sign: HmacKey::sign,
                        start: Tagging::start,
                    }
                },
            ),
        })
    }

    fn sign(&self, data: &[u8]) -> Digest {
        (self.ops.get().sign)(&self.key, data)
    }

    fn start(&self) -> Tagged {
        (self.ops.get().start)(&self.key)
    }
}

/// An in-progress computation with its hash's code, as [`Keying`].
struct Tagging<H: HmacHash> {
    hmac: Hmac<H>,
    ops: ZeroableRef<TagOps<H>>,
}

struct TagOps<H: HmacHash> {
    update: fn(&mut Hmac<H>, &[u8]),
    finish: fn(&Hmac<H>) -> Digest,
}

// Not derived, as for `HmacKey`.
impl<H: HmacHash> Clone for Tagging<H> {
    fn clone(&self) -> Self {
        Self {
            hmac: self.hmac.clone(),
            ops: self.ops,
        }
    }
}

impl<H: HmacHash> Tagging<H> {
    fn start(key: &HmacKey<H>) -> Tagged {
        H::tagged(Self {
            hmac: key.start(),
            ops: ZeroableRef::new(
                const {
                    &TagOps {
                        update: |hmac, data| hmac.update(data),
                        finish: Hmac::finish,
                    }
                },
            ),
        })
    }

    fn update(&mut self, data: &[u8]) {
        (self.ops.get().update)(&mut self.hmac, data)
    }

    fn finish(&self) -> Digest {
        (self.ops.get().finish)(&self.hmac)
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::*;

    #[test]
    fn acvp() {
        for (name, algorithm) in [
            ("HMAC-SHA-1-2.0", &HMAC_SHA1),
            ("HMAC-SHA2-256-2.0", &HMAC_SHA256),
            ("HMAC-SHA2-384-2.0", &HMAC_SHA384),
            ("HMAC-SHA2-512-2.0", &HMAC_SHA512),
        ] {
            for group in crate::test::acvp(name) {
                assert_eq!(group.str("testType"), "AFT");
                for test in group.tests() {
                    let key = Key::new(algorithm, &test.hex("key"));
                    let tag = sign(&key, &test.hex("msg"));
                    assert_eq!(&tag.as_ref()[..test.int("macLen") / 8], test.hex("mac"));
                }
            }
        }
    }

    #[test]
    fn smoke() {
        let key = Key::new(&HMAC_SHA256, b"hello");
        assert_eq!(sign(&key, b"world").as_ref(),
                   b"\xf1\xac\x97\x02\xeb\x5f\xaf\x23\xca\x29\x1a\x4d\xc4\x6d\xed\xde\xee\x2a\x78\xcc\xda\xf0\xa4\x12\xbe\xd7\x71\x4c\xff\xfb\x1c\xc4");

        let key = Key::new(&HMAC_SHA384, b"hello");
        assert_eq!(sign(&key, b"world").as_ref(),
                   b"\x80\xd0\x36\xd9\x97\x4e\x6f\x71\xce\xab\xe4\x93\xee\x89\x7d\x00\x23\x5e\xdc\xc4\xc7\x2e\x04\x6d\xdf\xc8\xbf\x68\xe8\x6a\x47\x7d\x63\xb9\xf7\xd2\x6a\xd5\xb9\x90\xaa\xe6\xac\x17\xdb\x57\xdd\xcf");

        let key = Key::new(&HMAC_SHA512, b"hello");
        assert_eq!(sign(&key, b"world").as_ref(),
                   b"\x66\x68\xed\x2f\x7d\x01\x6c\x5f\x12\xd7\x80\x8f\xc4\xf2\xd1\xdc\x48\x51\x62\x2d\x7f\x15\x61\x6d\xe9\x47\xa8\x23\xb3\xee\x67\xd7\x61\xb9\x53\xf0\x95\x60\xda\x30\x1f\x83\x29\x02\x02\r\xd1\xc6\x4f\x49\x6d\xf3\x7e\xb7\xac\x4f\xd2\xfe\xee\xb6\x7d\x77\xba\x9b");
    }

    #[test]
    fn verify_whole_tags_only() {
        for algorithm in ALGORITHMS {
            let key = Key::new(algorithm, b"key");
            let tag = sign(&key, b"message");
            assert_eq!(tag.as_ref().len(), algorithm.tag_len());
            assert_eq!(verify(&key, b"message", tag.as_ref()), Ok(()));

            let short = &tag.as_ref()[..algorithm.tag_len() - 1];
            assert_eq!(verify(&key, b"message", short), Err(Error::BadSignature));
            assert_eq!(verify(&key, b"message", &[]), Err(Error::BadSignature));
            let mut long = tag.as_ref().to_vec();
            long.push(0);
            assert_eq!(verify(&key, b"message", &long), Err(Error::BadSignature));
        }
    }

    #[test]
    fn secret_key_and_message() {
        // Under `admin/ctgrind`, nothing may branch on or index by the key or
        // message. Keys longer than a block are hashed first.
        for algorithm in ALGORITHMS {
            for key_len in [16, 200] {
                let key = vec![0x5a; key_len];
                let message = [0xa5; 300];
                let wanted = sign(&Key::new(algorithm, &key), &message);

                crate::low::ct::secret_slice(&key);
                crate::low::ct::secret_slice(&message);
                let key = Key::new(algorithm, &key);
                let mut ctx = Context::with_key(&key);
                ctx.update(&message[..100]);
                ctx.update(&message[100..]);
                assert_eq!(
                    crate::low::ct::into_public(ctx.sign()).as_ref(),
                    wanted.as_ref()
                );
                assert_eq!(verify(&key, &message, wanted.as_ref()), Ok(()));
            }
        }
    }

    // HMAC-SHA1 and HMAC-SHA256 on the SHA extensions, and HMAC-SHA384 and
    // HMAC-SHA512 on the SHA512 instructions, which valgrind cannot run, with
    // a secret key and message, for `admin/ct-sde`. The longer key is hashed
    // first, and the messages end in a block that pads within itself, fills
    // it exactly, pads into another, or follows a whole one, both in one call
    // and through a context's buffer.
    #[cfg(rind_backend = "x86_64")]
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_hmac() {
        use crate::low::ct_sde;

        assert!(is_x86_feature_detected!("sha"), "the SHA extensions");
        assert!(
            is_x86_feature_detected!("sha512"),
            "the SHA512 instructions"
        );
        let seed = ct_sde::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        for algorithm in [&HMAC_SHA1, &HMAC_SHA256, &HMAC_SHA384, &HMAC_SHA512] {
            for key_len in [16, 200] {
                for message_len in [300, 311, 316, 320] {
                    let (key, message) = (bytes(key_len), bytes(message_len));
                    ct_sde::traced(|| sign(&Key::new(algorithm, &key), &message));
                    ct_sde::traced(|| {
                        let mut ctx = Context::with_key(&Key::new(algorithm, &key));
                        ctx.update(&message);
                        ctx.sign()
                    });
                }
            }
        }
    }

    // What valgrind hides, as `ct_sde_hmac`, for `admin/ct-qemu`: HMAC-SHA1
    // and HMAC-SHA256 on armv7's crypto extension, and HMAC-SHA384 and
    // HMAC-SHA512 on aarch64's SHA-512 instructions, which rind takes only
    // with SHA3.
    #[cfg(any(rind_backend = "arm", rind_backend = "aarch64"))]
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_hmac() {
        use crate::low::{HaveCryptoExt, ct_qemu};

        assert!(HaveCryptoExt::check().is_some(), "the crypto extension");
        #[cfg(rind_backend = "arm")]
        let algorithms = [&HMAC_SHA1, &HMAC_SHA256];
        #[cfg(rind_backend = "aarch64")]
        let algorithms = {
            assert!(std::arch::is_aarch64_feature_detected!("sha3"), "SHA3");
            [&HMAC_SHA384, &HMAC_SHA512]
        };
        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        for algorithm in algorithms {
            for key_len in [16, 200] {
                let (key, message) = (bytes(key_len), bytes(300));
                ct_qemu::traced(|| sign(&Key::new(algorithm, &key), &message));
            }
        }
    }

    #[test]
    fn cavp() {
        #[derive(Debug, Default)]
        struct Cavp {
            algorithm: Option<&'static Algorithm>,
            key: Vec<u8>,
            message: Vec<u8>,
        }

        impl CavpSink for Cavp {
            fn on_meta(&mut self, meta: &str) {
                self.algorithm = match meta {
                    "L=20" => Some(&HMAC_SHA1),
                    // SHA-224, which rind does not offer.
                    "L=28" => None,
                    "L=32" => Some(&HMAC_SHA256),
                    "L=48" => Some(&HMAC_SHA384),
                    "L=64" => Some(&HMAC_SHA512),
                    _ => panic!("unhandled {meta:?}"),
                };
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "Klen" | "Tlen" => {}
                    "Count" => println!("  test {}", value.int()),
                    "Key" => self.key = value.bytes(),
                    "Msg" => self.message = value.bytes(),
                    "Mac" => {
                        let Some(algorithm) = self.algorithm else {
                            return;
                        };
                        let tag = sign(&Key::new(algorithm, &self.key), &self.message);
                        // Most vectors truncate the tag.
                        let wanted = value.bytes();
                        assert_eq!(&tag.as_ref()[..wanted.len()], wanted);
                    }
                    _ => {
                        todo!("{self:?} value {name} = {value:?}");
                    }
                }
            }
        }

        process_cavp("../thirdparty/cavp/hmac/HMAC.rsp", &mut Cavp::default());
    }

    static ALGORITHMS: [&Algorithm; 4] = [&HMAC_SHA1, &HMAC_SHA256, &HMAC_SHA384, &HMAC_SHA512];
}
