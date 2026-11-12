module
public import Rind.X86_64.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# The HMAC API's dispatch, modelled by hand

`Key`, `Context`, `sign`, and `verify` reach each hash's code through function
pointers, which Aeneas cannot translate, so the translation starts below them,
at `HmacKey` and `Hmac`, and this file models the Rust above them.
`admin/prove` fails unless this quote is still that Rust, so a change to it is
a change to this model:

```rust
pub struct Algorithm {
    id: Id,
    tag_len: usize,
    // The only path to the hash's code, so a binary links only the hashes
    // whose algorithms it names.
    key: fn(&[u8]) -> Keyed,
}

impl Algorithm {
    /// The length of this algorithm's tag, in bytes.
    pub fn tag_len(&self) -> usize {
        self.tag_len
    }
}

pub static HMAC_SHA1: Algorithm = Algorithm {
    id: Id::Sha1,
    tag_len: sha1::Sha1Context::OUTPUT_SZ,
    key: Keying::<LegacySha1>::with_key,
};

pub static HMAC_SHA256: Algorithm = Algorithm {
    id: Id::Sha256,
    tag_len: sha2::Sha256Context::OUTPUT_SZ,
    key: Keying::<Sha256>::with_key,
};

pub static HMAC_SHA384: Algorithm = Algorithm {
    id: Id::Sha384,
    tag_len: sha2::Sha384Context::OUTPUT_SZ,
    key: Keying::<Sha384>::with_key,
};

pub static HMAC_SHA512: Algorithm = Algorithm {
    id: Id::Sha512,
    tag_len: sha2::Sha512Context::OUTPUT_SZ,
    key: Keying::<Sha512>::with_key,
};

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

pub fn sign(key: &Key, data: &[u8]) -> Tag {
    let _entry = Entry::new_secret();
    Tag(key.0.sign(data))
}

pub fn verify(key: &Key, data: &[u8], tag: &[u8]) -> Result<(), Error> {
    let _entry = Entry::new_secret();
    match key.0.sign(data).ct_equal(tag) {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

pub struct Tag(Digest);

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

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

pub(super) struct Streaming(Tagged);

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

struct Keying<H: HmacHash> {
    key: HmacKey<H>,
    ops: ZeroableRef<KeyOps<H>>,
}

struct KeyOps<H: HmacHash> {
    algorithm: &'static Algorithm,
    sign: fn(&HmacKey<H>, &[u8]) -> Digest,
    start: fn(&HmacKey<H>) -> Tagged,
}

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

struct Tagging<H: HmacHash> {
    hmac: Hmac<H>,
    ops: ZeroableRef<TagOps<H>>,
}

struct TagOps<H: HmacHash> {
    update: fn(&mut Hmac<H>, &[u8]),
    finish: fn(&Hmac<H>) -> Digest,
}

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

```

The model departs from the Rust in three ways, and adds no axiom:

- `Keying<H>` is its key and `Tagging<H>` its `Hmac`: their `ops` are always
  the one `KeyOps` or `TagOps` of `H`'s own functions that `with_key` and
  `start` build, so a call through one is a call to that function.
  `admin/prove` checks that the quote holds every read of an `ops` in
  `high::hmac` and every `KeyOps` and `TagOps` it builds.
- An `Algorithm` is which static it is, as `Rind.X86_64.DigestAlgorithm`
  models the digest API's: its fields are private to `high::hmac`, which builds
  no other, and `admin/prove` checks that the quote holds every
  `= Algorithm {` there. Its `key` is `Keying::<H>::with_key` for the hash it
  names.
- `ZeroableRef` is the reference it holds, and wiping on drop is left out, as
  the translation leaves out every drop.
-/

namespace rind.x86_64

/-- SHA-1's `Hash` impl. -/
abbrev Sha1Hash := high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State

/-- SHA-256's `Hash` impl. -/
abbrev Sha256Hash := high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State

/-- SHA-384's `Hash` impl. -/
abbrev Sha384Hash := high.hash.Sha384.Insts.RindHighHashHashSha384ContextSha384State

/-- SHA-512's `Hash` impl. -/
abbrev Sha512Hash := high.hash.Sha512.Insts.RindHighHashHashSha512ContextSha512State

/-- `&'static Algorithm`: which of `high::hmac`'s statics. -/
inductive high.hmac.Algorithm where
  | HMAC_SHA1
  | HMAC_SHA256
  | HMAC_SHA384
  | HMAC_SHA512
deriving DecidableEq

/-- `Algorithm::tag_len`: the `OUTPUT_SZ` each static names. -/
def high.hmac.Algorithm.tag_len : high.hmac.Algorithm → Result Std.Usize
  | .HMAC_SHA1 => ok 20#usize
  | .HMAC_SHA256 => ok 32#usize
  | .HMAC_SHA384 => ok 48#usize
  | .HMAC_SHA512 => ok 64#usize

/-- The `HMAC_SHA1` static. -/
def high.hmac.HMAC_SHA1 : Result high.hmac.Algorithm := ok .HMAC_SHA1

/-- The `HMAC_SHA256` static. -/
def high.hmac.HMAC_SHA256 : Result high.hmac.Algorithm := ok .HMAC_SHA256

/-- The `HMAC_SHA384` static. -/
def high.hmac.HMAC_SHA384 : Result high.hmac.Algorithm := ok .HMAC_SHA384

/-- The `HMAC_SHA512` static. -/
def high.hmac.HMAC_SHA512 : Result high.hmac.Algorithm := ok .HMAC_SHA512

/-- `Keyed`, each variant's `Keying<H>` as its key. -/
inductive high.hmac.Keyed where
  | Sha1 (key : high.hmac.HmacKey high.hash.LegacySha1 high.hash.Sha1Context high.hash.Sha1State)
  | Sha256 (key : high.hmac.HmacKey high.hash.Sha256 high.hash.Sha256Context high.hash.Sha256State)
  | Sha384 (key : high.hmac.HmacKey high.hash.Sha384 high.hash.Sha384Context high.hash.Sha384State)
  | Sha512 (key : high.hmac.HmacKey high.hash.Sha512 high.hash.Sha512Context high.hash.Sha512State)

/-- `Key`. -/
@[reducible] def high.hmac.Key := high.hmac.Keyed

/-- `Tagged`, each variant's `Tagging<H>` as its `Hmac`. -/
inductive high.hmac.Tagged where
  | Sha1 (hmac : high.hmac.Hmac high.hash.LegacySha1 high.hash.Sha1Context high.hash.Sha1State)
  | Sha256 (hmac : high.hmac.Hmac high.hash.Sha256 high.hash.Sha256Context high.hash.Sha256State)
  | Sha384 (hmac : high.hmac.Hmac high.hash.Sha384 high.hash.Sha384Context high.hash.Sha384State)
  | Sha512 (hmac : high.hmac.Hmac high.hash.Sha512 high.hash.Sha512Context high.hash.Sha512State)

/-- `Streaming`. -/
@[reducible] def high.hmac.Streaming := high.hmac.Tagged

/-- `Context`. -/
@[reducible] def high.hmac.Context := high.hmac.Streaming

/-- `Tag`. -/
@[reducible] def high.hmac.Tag := high.digest.Digest

/-- `&[u8]`'s `AsRef<[u8]>`, through which `TagOps`'s `update` closure calls
`Hmac::update`: the slice itself. -/
def high.hmac.sliceAsRef : core.convert.AsRef (Slice Std.U8) (Slice Std.U8) :=
  { as_ref := ok }

/-- The function each static holds as `key`: `Keying::<H>::with_key`. -/
def high.hmac.Algorithm.key :
    high.hmac.Algorithm → Slice Std.U8 → Result high.hmac.Keyed
  | .HMAC_SHA1, key => do
    let key ← high.hmac.HmacKey.new Sha1Hash key
    ok (.Sha1 key)
  | .HMAC_SHA256, key => do
    let key ← high.hmac.HmacKey.new Sha256Hash key
    ok (.Sha256 key)
  | .HMAC_SHA384, key => do
    let key ← high.hmac.HmacKey.new Sha384Hash key
    ok (.Sha384 key)
  | .HMAC_SHA512, key => do
    let key ← high.hmac.HmacKey.new Sha512Hash key
    ok (.Sha512 key)

/-- `Keyed::sign`, through `Keying::sign`'s `ops.sign`, `HmacKey::sign`. -/
def high.hmac.Keyed.sign (self : high.hmac.Keyed) (data : Slice Std.U8) :
    Result high.digest.Digest :=
  match self with
  | .Sha1 key => high.hmac.HmacKey.sign Sha1Hash key data
  | .Sha256 key => high.hmac.HmacKey.sign Sha256Hash key data
  | .Sha384 key => high.hmac.HmacKey.sign Sha384Hash key data
  | .Sha512 key => high.hmac.HmacKey.sign Sha512Hash key data

/-- `Keyed::start`, through `Keying::start`'s `ops.start`, `Tagging::start`. -/
def high.hmac.Keyed.start : high.hmac.Keyed → Result high.hmac.Streaming
  | .Sha1 key => do
    let hmac ← high.hmac.HmacKey.start Sha1Hash key
    ok (.Sha1 hmac)
  | .Sha256 key => do
    let hmac ← high.hmac.HmacKey.start Sha256Hash key
    ok (.Sha256 hmac)
  | .Sha384 key => do
    let hmac ← high.hmac.HmacKey.start Sha384Hash key
    ok (.Sha384 hmac)
  | .Sha512 key => do
    let hmac ← high.hmac.HmacKey.start Sha512Hash key
    ok (.Sha512 hmac)

/-- `Key::new`. -/
def high.hmac.Key.new (algorithm : high.hmac.Algorithm) (key_value : Slice Std.U8) :
    Result high.hmac.Key := do
  let _ ← low.entry.Entry.new_secret
  algorithm.key key_value

/-- `Key::tag`. -/
def high.hmac.Key.tag (self : high.hmac.Key) (data : Slice Std.U8) : Result high.digest.Digest :=
  high.hmac.Keyed.sign self data

/-- `Key::start`. -/
def high.hmac.Key.start (self : high.hmac.Key) : Result high.hmac.Streaming :=
  high.hmac.Keyed.start self

/-- `Key::algorithm`: each variant's `ops.algorithm` is its hash's `HMAC`. -/
def high.hmac.Key.algorithm : high.hmac.Key → Result high.hmac.Algorithm
  | .Sha1 _ => ok .HMAC_SHA1
  | .Sha256 _ => ok .HMAC_SHA256
  | .Sha384 _ => ok .HMAC_SHA384
  | .Sha512 _ => ok .HMAC_SHA512

/-- `Streaming::update`, through `Tagging::update`'s `ops.update`, a closure
calling `Hmac::update`. -/
def high.hmac.Streaming.update (self : high.hmac.Streaming) (data : Slice Std.U8) :
    Result high.hmac.Streaming :=
  match self with
  | .Sha1 hmac => do
    let hmac ← high.hmac.Hmac.update Sha1Hash high.hmac.sliceAsRef hmac data
    ok (.Sha1 hmac)
  | .Sha256 hmac => do
    let hmac ← high.hmac.Hmac.update Sha256Hash high.hmac.sliceAsRef hmac data
    ok (.Sha256 hmac)
  | .Sha384 hmac => do
    let hmac ← high.hmac.Hmac.update Sha384Hash high.hmac.sliceAsRef hmac data
    ok (.Sha384 hmac)
  | .Sha512 hmac => do
    let hmac ← high.hmac.Hmac.update Sha512Hash high.hmac.sliceAsRef hmac data
    ok (.Sha512 hmac)

/-- `Streaming::finish`, through `Tagging::finish`'s `ops.finish`, `Hmac::finish`. -/
def high.hmac.Streaming.finish : high.hmac.Streaming → Result high.digest.Digest
  | .Sha1 hmac => high.hmac.Hmac.finish Sha1Hash hmac
  | .Sha256 hmac => high.hmac.Hmac.finish Sha256Hash hmac
  | .Sha384 hmac => high.hmac.Hmac.finish Sha384Hash hmac
  | .Sha512 hmac => high.hmac.Hmac.finish Sha512Hash hmac

/-- `Streaming`'s derived `Clone`, through `Tagging`'s, which clones the `Hmac`. -/
def high.hmac.Streaming.Insts.CoreCloneClone.clone : high.hmac.Streaming → Result high.hmac.Streaming
  | .Sha1 hmac => do
    let hmac ← high.hmac.Hmac.Insts.CoreCloneClone.clone Sha1Hash hmac
    ok (.Sha1 hmac)
  | .Sha256 hmac => do
    let hmac ← high.hmac.Hmac.Insts.CoreCloneClone.clone Sha256Hash hmac
    ok (.Sha256 hmac)
  | .Sha384 hmac => do
    let hmac ← high.hmac.Hmac.Insts.CoreCloneClone.clone Sha384Hash hmac
    ok (.Sha384 hmac)
  | .Sha512 hmac => do
    let hmac ← high.hmac.Hmac.Insts.CoreCloneClone.clone Sha512Hash hmac
    ok (.Sha512 hmac)

/-- `Context::with_key`. -/
def high.hmac.Context.with_key (key : high.hmac.Key) : Result high.hmac.Context :=
  high.hmac.Keyed.start key

/-- `Context::update`. -/
def high.hmac.Context.update (self : high.hmac.Context) (data : Slice Std.U8) :
    Result high.hmac.Context :=
  high.hmac.Streaming.update self data

/-- `Context::sign`. -/
def high.hmac.Context.sign (self : high.hmac.Context) : Result high.hmac.Tag := do
  let _ ← low.entry.Entry.new_secret
  high.hmac.Streaming.finish self

/-- `sign`. -/
def high.hmac.sign (key : high.hmac.Key) (data : Slice Std.U8) : Result high.hmac.Tag := do
  let _ ← low.entry.Entry.new_secret
  high.hmac.Keyed.sign key data

/-- `Digest::ct_equal`, quoted in `Rind.X86_64.DigestAlgorithm`. -/
def high.digest.Digest.ct_equal (self : high.digest.Digest) (other : Slice Std.U8) :
    Result Bool := do
  let s ← high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref self
  let b ← low.generic.ct_equal.ct_equal s other
  low.ct.into_public b

/-- `verify`. -/
def high.hmac.verify (key : high.hmac.Key) (data tag : Slice Std.U8) :
    Result (core.result.Result Unit error.Error) := do
  let _ ← low.entry.Entry.new_secret
  let d ← high.hmac.Keyed.sign key data
  let b ← high.digest.Digest.ct_equal d tag
  if b then ok (.Ok ()) else ok (.Err .BadSignature)

/-- `Tag`'s `AsRef<[u8]>`. -/
def high.hmac.Tag.Insts.CoreConvertAsRefSliceU8.as_ref (self : high.hmac.Tag) :
    Result (Slice Std.U8) :=
  high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref self

end rind.x86_64
