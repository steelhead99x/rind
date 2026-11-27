module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# The digest API's algorithms and digests, modelled by hand

`Algorithm` holds each hash's function pointers, which Aeneas cannot
translate, so the translation leaves it, its statics, and `output_len` opaque,
and this file models them, below the translation that reads them. `Digest`
holds a `&'static Algorithm`, which Aeneas cannot end a borrow of `Digest`
across, so it, and its methods that read its fields, are opaque too, and this
file models them as Aeneas translates them, with the algorithm by value.
`admin/prove` fails unless this quote is still that Rust, so a change to it is
a change to this model:

```rust
pub struct Algorithm {
    id: Id,
    output_len: usize,
    // The only paths to the hash's code, so a binary links only the hashes
    // whose algorithms it names.
    hash: fn(&[u8]) -> Digest,
    start: fn(&mut State, &[u8]),
}

impl Algorithm {
    /// The length of this algorithm's digest, in bytes.
    pub fn output_len(&self) -> usize {
        self.output_len
    }
}

pub static MD5: Algorithm = Algorithm {
    id: Id::Md5,
    output_len: md5::Md5Context::OUTPUT_SZ,
    hash: |data| Digest::new(&MD5, &md5::Md5State::new().finish_with(data)),
    start: Hashing::<Md5Context>::start,
};

pub static SHA1: Algorithm = Algorithm {
    id: Id::Sha1,
    output_len: sha1::Sha1Context::OUTPUT_SZ,
    hash: LegacySha1::hash,
    start: Hashing::<Sha1Context>::start,
};

pub static SHA256: Algorithm = Algorithm {
    id: Id::Sha256,
    output_len: sha2::Sha256Context::OUTPUT_SZ,
    hash: Sha256::hash,
    start: Hashing::<Sha256Context>::start,
};

pub static SHA384: Algorithm = Algorithm {
    id: Id::Sha384,
    output_len: sha2::Sha384Context::OUTPUT_SZ,
    hash: Sha384::hash,
    start: Hashing::<Sha384Context>::start,
};

pub static SHA512: Algorithm = Algorithm {
    id: Id::Sha512,
    output_len: sha2::Sha512Context::OUTPUT_SZ,
    hash: Sha512::hash,
    start: Hashing::<Sha512Context>::start,
};

pub static SHA512_256: Algorithm = Algorithm {
    id: Id::Sha512_256,
    output_len: sha2::Sha512_256Context::OUTPUT_SZ,
    hash: |data| {
        let output = sha2::Sha512_256Context::INITIAL.finish_with(data);
        Digest::new(&SHA512_256, &sha2::Sha512_256Context::truncate(&output))
    },
    start: Hashing::<Sha512_256Context>::start,
};

pub static SHA3_256: Algorithm = Algorithm {
    id: Id::Sha3_256,
    output_len: sha3::Sha3_256Context::OUTPUT_SZ,
    hash: one_shot::<Sha3_256Context>,
    start: Hashing::<Sha3_256Context>::start,
};

pub static SHA3_384: Algorithm = Algorithm {
    id: Id::Sha3_384,
    output_len: sha3::Sha3_384Context::OUTPUT_SZ,
    hash: one_shot::<Sha3_384Context>,
    start: Hashing::<Sha3_384Context>::start,
};

pub static SHA3_512: Algorithm = Algorithm {
    id: Id::Sha3_512,
    output_len: sha3::Sha3_512Context::OUTPUT_SZ,
    hash: one_shot::<Sha3_512Context>,
    start: Hashing::<Sha3_512Context>::start,
};

pub struct Digest {
    algorithm: &'static Algorithm,
    value: [u8; MAX_OUTPUT_LEN],
}

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

```

An `Algorithm` is which of these statics it is: its fields are private to
`high::digest`, which builds no other, and callers hold only `&'static`
references to them. `admin/prove` checks that the quote holds every
`= Algorithm {` in `high::digest`. Each output length is the `OUTPUT_SZ` the
static names, the length of the array its context's `finish` returns.
`Rind.X86_64.DigestDispatch` models `hash` and `start`, the function pointers.
-/

namespace rind.x86_64

/-- `&'static Algorithm`: which of `high::digest`'s statics. -/
inductive high.digest.Algorithm where
  | MD5
  | SHA1
  | SHA256
  | SHA384
  | SHA512
  | SHA512_256
  | SHA3_256
  | SHA3_384
  | SHA3_512
deriving DecidableEq

/-- `Algorithm::output_len`. -/
def high.digest.Algorithm.output_len : high.digest.Algorithm → Result Std.Usize
  | .MD5 => ok 16#usize
  | .SHA1 => ok 20#usize
  | .SHA256 => ok 32#usize
  | .SHA384 => ok 48#usize
  | .SHA512 => ok 64#usize
  | .SHA512_256 => ok 32#usize
  | .SHA3_256 => ok 32#usize
  | .SHA3_384 => ok 48#usize
  | .SHA3_512 => ok 64#usize

/-- The `MD5` static. -/
def high.digest.MD5 : Result high.digest.Algorithm := ok .MD5

/-- The `SHA1` static. -/
def high.digest.SHA1 : Result high.digest.Algorithm := ok .SHA1

/-- The `SHA256` static. -/
def high.digest.SHA256 : Result high.digest.Algorithm := ok .SHA256

/-- The `SHA384` static. -/
def high.digest.SHA384 : Result high.digest.Algorithm := ok .SHA384

/-- The `SHA512` static. -/
def high.digest.SHA512 : Result high.digest.Algorithm := ok .SHA512

/-- The `SHA512_256` static. -/
def high.digest.SHA512_256 : Result high.digest.Algorithm := ok .SHA512_256

/-- The `SHA3_256` static. -/
def high.digest.SHA3_256 : Result high.digest.Algorithm := ok .SHA3_256

/-- The `SHA3_384` static. -/
def high.digest.SHA3_384 : Result high.digest.Algorithm := ok .SHA3_384

/-- The `SHA3_512` static. -/
def high.digest.SHA3_512 : Result high.digest.Algorithm := ok .SHA3_512

/-- `Digest`. -/
structure high.digest.Digest where
  algorithm : high.digest.Algorithm
  value : Std.Array Std.U8 64#usize

/-- `Digest::zeroed`. -/
def high.digest.Digest.zeroed (algorithm : high.digest.Algorithm) : Result high.digest.Digest := do
  let a := Std.Array.repeat 64#usize 0#u8
  ok { algorithm, value := a }

/-- `Digest::as_mut`. -/
def high.digest.Digest.as_mut (self : high.digest.Digest) :
    Result ((Slice Std.U8) × (Slice Std.U8 → high.digest.Digest)) := do
  let i ← high.digest.Algorithm.output_len self.algorithm
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) self.value
      { «end» := i }
  let back := fun s1 => let a := index_mut_back s1
                        { self with value := a }
  ok (s, back)

/-- `Digest`'s `AsRef<[u8]>`. -/
def high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref (self : high.digest.Digest) :
    Result (Slice Std.U8) := do
  let i ← high.digest.Algorithm.output_len self.algorithm
  core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) self.value
    { «end» := i }

end rind.x86_64
