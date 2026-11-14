module
public import Rind.X86_64.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

/-!
# The AEAD API's dispatch, modelled by hand

`Key` reaches each cipher's `Cipher` impl through function pointers, which
Aeneas cannot translate: `Algorithm`'s `expand`, and `Sealer`'s `Ops`. The
translation starts below them, at the `Cipher` impls, and this file models
the Rust above them. `admin/prove` fails unless these quotes are still that
Rust, so a change to it is a change to this model:

```rust
pub struct Algorithm {
    id: AlgorithmId,
    // The only path to the cipher's code, so a binary links only the ciphers
    // whose algorithms it names.
    expand: fn(&[u8]) -> Inner,
}

impl Algorithm {
    /// The length of a key, in bytes.
    pub fn key_len(&self) -> usize {
        match self.id {
            AlgorithmId::Aes128Gcm => 16,
            AlgorithmId::Aes192Gcm => 24,
            AlgorithmId::Aes256Gcm | AlgorithmId::ChaCha20Poly1305 => 32,
        }
    }

    /// The length of a tag, in bytes.
    pub fn tag_len(&self) -> usize {
        TAG_LEN
    }

    /// The length of a nonce, in bytes.
    pub fn nonce_len(&self) -> usize {
        NONCE_LEN
    }
}

pub static AES_128_GCM: Algorithm = Algorithm {
    id: AlgorithmId::Aes128Gcm,
    expand: Sealer::<AesGcm>::expand,
};

pub static AES_192_GCM: Algorithm = Algorithm {
    id: AlgorithmId::Aes192Gcm,
    expand: Sealer::<AesGcm>::expand,
};

pub static AES_256_GCM: Algorithm = Algorithm {
    id: AlgorithmId::Aes256Gcm,
    expand: Sealer::<AesGcm>::expand,
};

pub static CHACHA20_POLY1305: Algorithm = Algorithm {
    id: AlgorithmId::ChaCha20Poly1305,
    expand: Sealer::<ChaCha20Poly1305>::expand,
};

impl Key {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not [`Algorithm::key_len`] bytes.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        if key.len() != algorithm.key_len() {
            return Err(Error::WrongLength);
        }

        Ok(Self((algorithm.expand)(key)))
    }

    /// Encrypts `in_out` in place and returns the tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `in_out` or `aad` is past the algorithm's limit: 2^36 - 32 and 2^61 - 1
    /// bytes for AES-GCM, and 2^38 - 64 bytes of `in_out` for
    /// ChaCha20-Poly1305.
    pub fn seal_in_place_separate_tag(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        let mut tag = [0u8; TAG_LEN];
        match &self.0 {
            Inner::AesGcm(key) => key.seal(&nonce.0, aad, in_out, &mut tag),
            Inner::ChaCha20Poly1305(key) => key.seal(&nonce.0, aad, in_out, &mut tag),
        }?;
        Ok(Tag(tag))
    }

    /// Encrypts `in_out` in place and appends the tag to it.
    ///
    /// Fails as [`Self::seal_in_place_separate_tag`] does.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let tag = self.seal_in_place_separate_tag(nonce, aad, in_out.as_mut())?;
        in_out.extend(tag.as_ref());
        Ok(())
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag, and
    /// returns the plaintext at its front.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag or
    /// does not verify, clearing the ciphertext in the latter case, and with
    /// [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let (in_out, tag) = in_out.split_last_chunk_mut().ok_or(Error::DecryptFailed)?;
        self.open_in_place_separate_tag(nonce, aad, Tag(*tag), in_out)
    }

    /// Decrypts and verifies `in_out` against the separate `tag`, and returns
    /// the plaintext.
    ///
    /// Fails with [`Error::DecryptFailed`], clearing `in_out`, if it does not
    /// verify, and with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place_separate_tag<'a>(
        &self,
        nonce: Nonce,
        aad: &[u8],
        tag: Tag,
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        match &self.0 {
            Inner::AesGcm(key) => key.open(&nonce.0, aad, in_out, &tag.0),
            Inner::ChaCha20Poly1305(key) => key.open(&nonce.0, aad, in_out, &tag.0),
        }?;
        Ok(in_out)
    }
}

struct Sealer<C: Cipher> {
    key: ManuallyDrop<C>,
    ops: ZeroableRef<Ops<C>>,
}

type Seal<C> = fn(&C, &[u8; NONCE_LEN], &[u8], &mut [u8], &mut [u8; TAG_LEN]) -> Result<(), Error>;

type Open<C> = fn(&C, &[u8; NONCE_LEN], &[u8], &mut [u8], &[u8; TAG_LEN]) -> Result<(), Error>;

struct Ops<C> {
    seal: Seal<C>,
    open: Open<C>,
}

impl<C: Cipher> Sealer<C> {
    /// Expands `key` into an [`Inner`].
    ///
    /// Not inlined, so each function wraps a value in one layer, and LLVM
    /// builds it in the caller's slot: two layers in one function, as
    /// `Ok(Key(Inner::AesGcm(..)))`, copied the whole key twice.
    #[inline(never)]
    fn expand(key: &[u8]) -> Inner {
        C::inner(Self {
            key: ManuallyDrop::new(C::new(key)),
            ops: ZeroableRef::new(
                const {
                    &Ops {
                        seal: C::seal,
                        open: C::open,
                    }
                },
            ),
        })
    }

    fn seal(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &mut [u8; TAG_LEN],
    ) -> Result<(), Error> {
        (self.ops.get().seal)(&self.key, nonce, aad, in_out, tag)
    }

    fn open(
        &self,
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        in_out: &mut [u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), Error> {
        (self.ops.get().open)(&self.key, nonce, aad, in_out, tag)
    }
}

pub struct Nonce([u8; NONCE_LEN]);

impl Nonce {
    /// Wraps `nonce`, which the caller promises is never reused with the same key.
    pub fn assume_unique_for_key(nonce: [u8; NONCE_LEN]) -> Self {
        Self(nonce)
    }
}

pub struct Tag([u8; TAG_LEN]);

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

pub struct RandomizedNonceKey(XChaCha20Poly1305);

impl RandomizedNonceKey {
    /// Makes a key from 32 bytes of key material.
    pub fn new(key: &[u8; 32]) -> Self {
        Self(XChaCha20Poly1305::new(*key))
    }

    /// Encrypts `in_out` in place under a fresh random nonce, appends the tag,
    /// and returns the nonce, which the opener needs.
    ///
    /// Fails with [`Error::RngFailed`] if the system random source does, or
    /// with [`Error::WrongLength`], leaving `in_out` unchanged, if it is longer
    /// than 2^38 - 64 bytes.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<RandomNonce, Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let mut nonce = [0u8; 24];
        SystemRandom.fill(&mut nonce)?;
        let mut tag = [0u8; TAG_LEN];
        self.0.encrypt(&nonce, aad, in_out.as_mut(), &mut tag)?;
        in_out.extend(&tag);
        Ok(RandomNonce(nonce))
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag,
    /// sealed under `nonce`, and returns the plaintext at its front.
    ///
    /// Fails as [`Key::open_in_place`] does.
    pub fn open_in_place<'a>(
        &self,
        nonce: RandomNonce,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let (in_out, tag) = in_out.split_last_chunk_mut().ok_or(Error::DecryptFailed)?;
        self.0.decrypt(&nonce.0, aad, in_out, tag)?;
        Ok(in_out)
    }
}

pub struct RandomNonce([u8; 24]);

impl AsRef<[u8]> for RandomNonce {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 24]> for RandomNonce {
    fn from(nonce: [u8; 24]) -> Self {
        Self(nonce)
    }
}

```

The model departs from the Rust in four ways, and adds no axiom:

- `Sealer<C>` is its key, and `Sealer`'s `seal` and `open` call `C`'s
  directly: `Sealer` and `Ops` are private to `aead`, where only
  `Sealer::expand` builds one, of `C::seal` and `C::open`. `admin/prove`
  checks that the quote holds every mention of `Ops` there, and every
  `Algorithm` it builds.
- `ManuallyDrop<C>` and `ZeroableRef<T>` are their `T`: drops are not
  modelled, as everywhere in the translation.
- `?` is a `match`, since each error it passes on is already an `Error`.
- `open_in_place` returns the bytes before the tag, which it opens in place,
  and `split_last_chunk_mut` is `take` and `drop`; so does
  `RandomizedNonceKey`'s.

Each `seal_in_place_append_tag` takes `InOut`'s `AsMut<[u8]>` and `Extend<&u8>`
impls as arguments, Aeneas's structures for those traits, as the translation
passes a trait bound; `Extend` receives the shared borrow `&u8` as the `U8`
Aeneas reads it as, and the tag through the slice iterator that `&[u8]`'s
`IntoIterator` impl makes.

`RandomizedNonceKey`'s draws its nonce through `SystemRandom`'s
`RandomSource` impl, which the translation holds.
-/

namespace rind.x86_64

/-- `Nonce`. -/
structure aead.Nonce where
  bytes : Std.Array U8 12#usize

/-- `Nonce::assume_unique_for_key`. -/
def aead.Nonce.assume_unique_for_key (nonce : Std.Array U8 12#usize) : aead.Nonce := ⟨nonce⟩

/-- `Tag`. -/
structure aead.Tag where
  bytes : Std.Array U8 16#usize

/-- `Algorithm`. -/
structure aead.Algorithm where
  id : aead.AlgorithmId
  expand : Slice U8 → Result aead.Inner

/-- `Algorithm::key_len`. -/
def aead.Algorithm.key_len (self : aead.Algorithm) : Usize :=
  match self.id with
  | .Aes128Gcm => 16#usize
  | .Aes192Gcm => 24#usize
  | .Aes256Gcm | .ChaCha20Poly1305 => 32#usize

/-- `Sealer::<C>::expand`, whose `ops` are `C::seal` and `C::open`. -/
def aead.Sealer.expand {C : Type} (CipherInst : aead.Cipher C) (key : Slice U8) : Result aead.Inner := do
  let k ← CipherInst.new key
  CipherInst.inner k

/-- `Sealer::<C>::seal`, whose `ops.seal` is `C::seal`. -/
def aead.Sealer.seal {C : Type} (CipherInst : aead.Cipher C) (self : aead.Sealer C)
    (nonce : Std.Array U8 12#usize) (aad in_out : Slice U8) (tag : Std.Array U8 16#usize) :
    Result ((core.result.Result Unit error.Error) × Slice U8 × Std.Array U8 16#usize) :=
  CipherInst.seal self nonce aad in_out tag

/-- `Sealer::<C>::open`, whose `ops.open` is `C::open`. -/
def aead.Sealer.open {C : Type} (CipherInst : aead.Cipher C) (self : aead.Sealer C)
    (nonce : Std.Array U8 12#usize) (aad in_out : Slice U8) (tag : Std.Array U8 16#usize) :
    Result ((core.result.Result Unit error.Error) × Slice U8) :=
  CipherInst.open self nonce aad in_out tag

/-- The `AES_128_GCM` static. -/
def aead.AES_128_GCM : aead.Algorithm where
  id := .Aes128Gcm
  expand := aead.Sealer.expand mid.aes_gcm.AesGcm.Insts.RindAeadCipher

/-- The `AES_192_GCM` static. -/
def aead.AES_192_GCM : aead.Algorithm where
  id := .Aes192Gcm
  expand := aead.Sealer.expand mid.aes_gcm.AesGcm.Insts.RindAeadCipher

/-- The `AES_256_GCM` static. -/
def aead.AES_256_GCM : aead.Algorithm where
  id := .Aes256Gcm
  expand := aead.Sealer.expand mid.aes_gcm.AesGcm.Insts.RindAeadCipher

/-- The `CHACHA20_POLY1305` static. -/
def aead.CHACHA20_POLY1305 : aead.Algorithm where
  id := .ChaCha20Poly1305
  expand := aead.Sealer.expand mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher
/-- `Key::new`. -/
def aead.Key.new (algorithm : aead.Algorithm) (key : Slice U8) :
    Result (core.result.Result aead.Key error.Error) :=
  if key.len ≠ algorithm.key_len then ok (.Err .WrongLength)
  else do
    let inner ← algorithm.expand key
    ok (.Ok inner)

/-- `Key::seal_in_place_separate_tag`. -/
def aead.Key.seal_in_place_separate_tag (self : aead.Key) (nonce : aead.Nonce) (aad in_out : Slice U8) :
    Result ((core.result.Result aead.Tag error.Error) × Slice U8) := do
  let tag := Std.Array.repeat 16#usize 0#u8
  let (r, in_out, tag) ← match self with
    | .AesGcm key => aead.Sealer.seal mid.aes_gcm.AesGcm.Insts.RindAeadCipher key nonce.bytes aad in_out tag
    | .ChaCha20Poly1305 key =>
      aead.Sealer.seal mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher key nonce.bytes aad in_out tag
  match r with
  | .Ok () => ok (.Ok ⟨tag⟩, in_out)
  | .Err e => ok (.Err e, in_out)

/-- `Key::seal_in_place_append_tag`: seals the buffer's `as_mut` view, then
hands the tag to its `extend`. -/
def aead.Key.seal_in_place_append_tag {InOut : Type} (AsMutInst : core.convert.AsMut InOut (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend InOut U8) (self : aead.Key) (nonce : aead.Nonce)
    (aad : Slice U8) (in_out : InOut) : Result ((core.result.Result Unit error.Error) × InOut) := do
  let (view, back) ← AsMutInst.as_mut in_out
  let (r, view) ← aead.Key.seal_in_place_separate_tag self nonce aad view
  let in_out := back view
  match r with
  | .Ok tag =>
    let in_out ← ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) in_out
      tag.bytes.to_slice
    ok (.Ok (), in_out)
  | .Err e => ok (.Err e, in_out)

/-- `Key::open_in_place_separate_tag`. -/
def aead.Key.open_in_place_separate_tag (self : aead.Key) (nonce : aead.Nonce) (aad : Slice U8)
    (tag : aead.Tag) (in_out : Slice U8) : Result ((core.result.Result (Slice U8) error.Error) × Slice U8) := do
  let (r, in_out) ← match self with
    | .AesGcm key => aead.Sealer.open mid.aes_gcm.AesGcm.Insts.RindAeadCipher key nonce.bytes aad in_out tag.bytes
    | .ChaCha20Poly1305 key =>
      aead.Sealer.open mid.chacha20poly1305.ChaCha20Poly1305.Insts.RindAeadCipher key nonce.bytes aad in_out
        tag.bytes
  match r with
  | .Ok () => ok (.Ok in_out, in_out)
  | .Err e => ok (.Err e, in_out)

/-- `Key::open_in_place`: the tag is the last 16 bytes of `in_out`, which is
refused if shorter. Returns the result and the bytes before the tag, which
the call decrypts in place. -/
def aead.Key.open_in_place (self : aead.Key) (nonce : aead.Nonce) (aad in_out : Slice U8) :
    Result ((core.result.Result (Slice U8) error.Error) × Slice U8) :=
  if in_out.length < 16 then ok (.Err .DecryptFailed, in_out)
  else
    let body := Slice.from (in_out.val.take (in_out.length - 16)) (by
      have := in_out.property; simp only [List.length_take]; omega)
    if h : (in_out.val.drop (in_out.length - 16)).length = 16 then
      aead.Key.open_in_place_separate_tag self nonce aad
        ⟨Std.Array.from (in_out.val.drop (in_out.length - 16)) h⟩ body
    else fail .panic
/-- `RandomizedNonceKey`. -/
structure aead.RandomizedNonceKey where
  key : mid.xchacha20poly1305.XChaCha20Poly1305
/-- `RandomNonce`. -/
structure aead.RandomNonce where
  bytes : Std.Array U8 24#usize
/-- `RandomNonce`'s `From<[u8; 24]>`. -/
def aead.RandomNonce.from (nonce : Std.Array U8 24#usize) : aead.RandomNonce := ⟨nonce⟩
/-- `RandomizedNonceKey::new`. -/
def aead.RandomizedNonceKey.new (key : Std.Array U8 32#usize) : Result aead.RandomizedNonceKey := do
  let k ← mid.xchacha20poly1305.XChaCha20Poly1305.new key
  ok ⟨k⟩
/-- `RandomizedNonceKey::seal_in_place_append_tag`: draws the nonce, seals the
buffer's `as_mut` view, then hands the tag to its `extend`. -/
def aead.RandomizedNonceKey.seal_in_place_append_tag {InOut : Type}
    (AsMutInst : core.convert.AsMut InOut (Slice U8)) (ExtendInst : core.iter.traits.collect.Extend InOut U8)
    (self : aead.RandomizedNonceKey) (aad : Slice U8) (in_out : InOut) :
    Result ((core.result.Result aead.RandomNonce error.Error) × InOut) := do
  let (s, to_slice_mut_back) ← lift (Std.Array.to_slice_mut (Std.Array.repeat 24#usize 0#u8))
  let (r, _, s) ← mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill () s
  match r with
  | .Err e => ok (.Err e, in_out)
  | .Ok () =>
    let nonce := to_slice_mut_back s
    let (view, back) ← AsMutInst.as_mut in_out
    let (r, view, tag) ← mid.xchacha20poly1305.XChaCha20Poly1305.encrypt self.key nonce aad view
      (Std.Array.repeat 16#usize 0#u8)
    let in_out := back view
    match r with
    | .Err e => ok (.Err e, in_out)
    | .Ok () =>
      let in_out ← ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) in_out
        tag.to_slice
      ok (.Ok ⟨nonce⟩, in_out)
/-- `RandomizedNonceKey::open_in_place`: the tag is the last 16 bytes of
`in_out`, which is refused if shorter. Returns the result and the bytes before
the tag, which the call decrypts in place. -/
def aead.RandomizedNonceKey.open_in_place (self : aead.RandomizedNonceKey) (nonce : aead.RandomNonce)
    (aad in_out : Slice U8) : Result ((core.result.Result (Slice U8) error.Error) × Slice U8) :=
  if in_out.length < 16 then ok (.Err .DecryptFailed, in_out)
  else
    let body := Slice.from (in_out.val.take (in_out.length - 16)) (by
      have := in_out.property; simp only [List.length_take]; omega)
    if h : (in_out.val.drop (in_out.length - 16)).length = 16 then do
      let (r, body) ← mid.xchacha20poly1305.XChaCha20Poly1305.decrypt self.key nonce.bytes aad body
        (Std.Array.from (in_out.val.drop (in_out.length - 16)) h)
      match r with
      | .Ok () => ok (.Ok body, body)
      | .Err e => ok (.Err e, body)
    else fail .panic

end rind.x86_64
