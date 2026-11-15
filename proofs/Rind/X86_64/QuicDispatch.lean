module
public import Rind.X86_64.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

/-!
# The header-protection API's dispatch, modelled by hand

`HeaderProtectionKey` reaches each cipher's `Mask` impl through function
pointers, which Aeneas cannot translate, so the translation starts below them
and this file models the Rust above them. `admin/prove` fails unless these
quotes are still that Rust, so a change to it is a change to this model:

```rust
pub(crate) struct ZeroableRef<T: 'static>(Option<&'static T>);

impl<T> ZeroableRef<T> {
    pub(crate) const fn new(value: &'static T) -> Self {
        Self(Some(value))
    }

    pub(crate) fn get(&self) -> &'static T {
        self.0.expect("wiped only on drop")
    }
}

pub struct Algorithm {
    id: AlgorithmId,
    // The only path to the cipher's code, so a binary links only the ciphers
    // whose algorithms it names.
    new: fn(&[u8]) -> Result<Key, Error>,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        match self.id {
            AlgorithmId::Aes128 => 16,
            AlgorithmId::Aes256 | AlgorithmId::ChaCha20 => 32,
        }
    }
}

pub static CHACHA20: Algorithm = Algorithm {
    id: AlgorithmId::ChaCha20,
    new: |key| {
        let key = key.try_into().map_err(|_| Error::WrongLength)?;
        Ok(Key::ChaCha20(Masker::new(ChaCha20::new(key))))
    },
};

impl HeaderProtectionKey {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        Ok(Self((algorithm.new)(key)?))
    }

    /// Computes the mask for `sample`: its first byte masks the packet's first
    /// byte, and the rest mask the packet number.
    pub fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        match &self.0 {
            Key::Aes(key) => key.mask(sample),
            Key::ChaCha20(key) => key.mask(sample),
        }
    }
}

struct Masker<C: Mask> {
    key: C,
    mask: ZeroableRef<MaskFn<C>>,
}

type MaskFn<C> = fn(&C, &[u8; SAMPLE_LEN]) -> [u8; 5];

impl<C: Mask> Masker<C> {
    fn new(key: C) -> Self {
        Self {
            key,
            mask: ZeroableRef::new(const { &(C::mask as MaskFn<C>) }),
        }
    }

    fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> [u8; 5] {
        (self.mask.get())(&self.key, sample)
    }
}

```

The model departs from the Rust in three ways, and adds no axiom:

- `Masker<C>` is its key, and `Masker::mask` calls `C`'s `mask` directly:
  `Masker`'s fields are private to `aead::quic`, where only `Masker::new`
  builds one, with `C::mask`. `admin/prove` checks that the quote holds every
  `Masker` literal and `impl` there, and every write to a `mask` field.
- `ZeroableRef<T>` is its `T`: only the drop that wipes it leaves it `None`.
- `?` is a `match`, since each error it passes on is already an `Error`, and
  `map_err(|_| Error::WrongLength)?` a `match` returning that error.

Drops are not modelled, as everywhere in the translation. Of the
header-protection statics, only `CHACHA20` is here: each target's
`Dispatch.lean`, where its translation reaches AES key setup (armv7's does
not), models the AES ones. `admin/prove` writes the aarch64, armv7, and
portable models from this file by renaming the target.
-/

namespace rind.x86_64

/-- `quic::Algorithm`. -/
structure aead.quic.Algorithm where
  id : aead.quic.AlgorithmId
  new : Slice Std.U8 → Result (core.result.Result aead.quic.Key error.Error)

/-- `quic::Algorithm::key_len`. -/
def aead.quic.Algorithm.key_len (self : aead.quic.Algorithm) : Usize :=
  match self.id with
  | .Aes128 => 16#usize
  | .Aes256 | .ChaCha20 => 32#usize

/-- `Masker::<C>::new`, whose `mask` is `C::mask`. -/
def aead.quic.Masker.new {C : Type} (key : C) : Result (aead.quic.Masker C) :=
  ok key

/-- `Masker::<C>::mask`, whose `mask` is `C::mask`. -/
def aead.quic.Masker.mask {C : Type} (MaskInst : aead.quic.Mask C) (self : aead.quic.Masker C)
    (sample : Array Std.U8 16#usize) : Result (Array Std.U8 5#usize) :=
  MaskInst.mask self sample

/-- The `CHACHA20` static. -/
def aead.quic.CHACHA20 : aead.quic.Algorithm where
  id := .ChaCha20
  new key := do
    let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 key
    match r with
    | .Ok key =>
      let c ← mid.chacha20.ChaCha20.new key
      let m ← aead.quic.Masker.new c
      ok (.Ok (.ChaCha20 m))
    | .Err _ => ok (.Err .WrongLength)

/-- `HeaderProtectionKey::new`. -/
def aead.quic.HeaderProtectionKey.new (algorithm : aead.quic.Algorithm) (key : Slice Std.U8) :
    Result (core.result.Result aead.quic.HeaderProtectionKey error.Error) := do
  let r ← algorithm.new key
  match r with
  | .Ok k => ok (.Ok k)
  | .Err e => ok (.Err e)

/-- `HeaderProtectionKey::mask`. -/
def aead.quic.HeaderProtectionKey.mask (self : aead.quic.HeaderProtectionKey)
    (sample : Array Std.U8 16#usize) : Result (Array Std.U8 5#usize) :=
  match self with
  | .Aes key => aead.quic.Masker.mask mid.aes.Aes.Insts.RindAeadQuicMask key sample
  | .ChaCha20 key => aead.quic.Masker.mask mid.chacha20.ChaCha20.Insts.RindAeadQuicMask key sample

end rind.x86_64
