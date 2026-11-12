import Rind.X86_64.AesGcm
import Rind.X86_64.AeadDispatch
open Aeneas Aeneas.Std Result rind.vale

/-!
# AES-GCM's custom-IV key, modelled by hand

`aead::gcm::Key` takes an IV of any length and makes tags of one `TagLength`,
over an `aead::Key`, whose dispatch `Rind.X86_64.AeadDispatch` models by hand,
since its cipher is reached through function pointers. This file models
`gcm::Key` by hand over that model, and `admin/prove` fails unless these quotes
are still the Rust they model, so a change to that Rust is a change to this
model:

```rust
pub enum TagLength {
    /// The whole 128-bit tag.
    Full,
    /// The first 120 bits of the tag.
    Truncated120,
    /// The first 112 bits of the tag.
    Truncated112,
    /// The first 104 bits of the tag.
    Truncated104,
    /// The first 96 bits of the tag.
    Truncated96,
    /// The first 64 bits of the tag.
    Truncated64,
    /// The first 32 bits of the tag.
    Truncated32,
}

impl TagLength {
    fn bytes(self) -> usize {
        match self {
            Self::Full => 16,
            Self::Truncated120 => 15,
            Self::Truncated112 => 14,
            Self::Truncated104 => 13,
            Self::Truncated96 => 12,
            Self::Truncated64 => 8,
            Self::Truncated32 => 4,
        }
    }
}

pub struct Iv<'a>(&'a [u8]);

pub struct Key {
    // An `aead::Key`, so a 96-bit IV takes its path, the one `proofs/` covers
    // on x86_64, compiled as when it had no other caller.
    key: ManuallyDrop<super::Key>,
    tag_len: TagLength,
}

impl Key {
    /// Expands `key` for `algorithm`, to make tags of `tag_len`, failing with
    /// [`Error::WrongLength`] if it is not that algorithm's key length.
    pub fn new(
        algorithm: &'static Algorithm,
        key: &[u8],
        tag_len: TagLength,
    ) -> Result<Self, Error> {
        let aead = match algorithm.key_len {
            16 => &AES_128_GCM,
            24 => &AES_192_GCM,
            _ => &AES_256_GCM,
        };
        if key.len() != algorithm.key_len {
            return Err(Error::WrongLength);
        }
        Ok(Self {
            key: ManuallyDrop::new(super::Key::new(aead, key)?),
            tag_len,
        })
    }

    fn aes_gcm(&self) -> &AesGcm {
        match &self.key.0 {
            Inner::AesGcm(sealer) => &sealer.key,
            Inner::ChaCha20Poly1305(_) => unreachable!("`new` expands only AES"),
        }
    }

    /// The length of this key's tags, in bytes.
    pub fn tag_len(&self) -> usize {
        self.tag_len.bytes()
    }

    /// Encrypts `in_out` in place under `iv` and returns the tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `aad` or `in_out` is past GCM's limit: 2^61 - 1 and 2^36 - 32 bytes.
    pub fn seal_in_place_separate_tag(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        let mut tag = Tag {
            bytes: [0; 16],
            len: self.tag_len(),
        };
        match iv.0.try_into() {
            Ok(nonce) => {
                let nonce = Nonce::assume_unique_for_key(nonce);
                tag.bytes = self.key.seal_in_place_separate_tag(nonce, aad, in_out)?.0;
            }
            Err(_) => {
                self.aes_gcm()
                    .encrypt_any(iv.0, aad, in_out, &mut tag.bytes[..tag.len])?;
            }
        }
        Ok(tag)
    }

    /// Encrypts `in_out` in place under `iv` and appends the tag to it.
    ///
    /// Fails as [`Self::seal_in_place_separate_tag`] does.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let tag = self.seal_in_place_separate_tag(iv, aad, in_out.as_mut())?;
        in_out.extend(tag.as_ref());
        Ok(())
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag of
    /// [`Self::tag_len`] bytes, and returns the plaintext at its front.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag
    /// or does not verify, clearing the ciphertext in the latter case, and
    /// with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let at = in_out
            .len()
            .checked_sub(self.tag_len())
            .ok_or(Error::DecryptFailed)?;
        let (in_out, tag) = in_out.split_at_mut(at);
        self.open(iv, aad, tag, in_out)?;
        Ok(in_out)
    }

    /// Decrypts and verifies `in_out` against the separate `tag`, and returns
    /// the plaintext.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `tag` is not [`Self::tag_len`] bytes or past the sealing limits, and
    /// with [`Error::DecryptFailed`], clearing `in_out`, if it does not
    /// verify.
    pub fn open_in_place_separate_tag<'a>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        tag: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        if tag.len() != self.tag_len() {
            return Err(Error::WrongLength);
        }
        self.open(iv, aad, tag, in_out)?;
        Ok(in_out)
    }

    /// Opens `in_out` against `tag`, of this key's length.
    fn open(&self, iv: Iv<'_>, aad: &[u8], tag: &[u8], in_out: &mut [u8]) -> Result<(), Error> {
        match (iv.0.try_into(), tag.try_into()) {
            (Ok(nonce), Ok(tag)) => {
                let nonce = Nonce::assume_unique_for_key(nonce);
                self.key
                    .open_in_place_separate_tag(nonce, aad, super::Tag(tag), in_out)?;
            }
            _ => self.aes_gcm().decrypt_any(iv.0, aad, in_out, tag)?,
        }
        Ok(())
    }
}

pub struct Tag {
    bytes: [u8; 16],
    len: usize,
}

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

```

The model departs from the Rust in these ways, and adds no axiom:

- `ManuallyDrop<super::Key>` is its `super::Key`: drops are not modelled, as
  everywhere in the translation, and neither are the `Debug` and `Drop` impls.
- `aes_gcm()` only supplies the receiver of `encrypt_any` and `decrypt_any`,
  which are not modelled, so it is not either.
- `Iv::assume_unique_for_key` is not modelled: its check is the caller's
  precondition, so an `Iv` here is its bytes.
- The arm for an IV that is not 12 bytes, which runs `encrypt_any` or
  `decrypt_any`, and `open`'s arm for a tag that is not 16 bytes, are opaque.
  They run rind's by-8 kernels, which no proof covers (`proofs/README.md`), so
  no theorem here reads them.
- `Tag::as_ref`'s `[..len]` is `take len`: a tag's `len` is one of the lengths
  `TagLength` names, all within its 16 bytes.
-/

namespace rind.x86_64

/-- `TagLength`. -/
inductive aead.gcm.TagLength where
| Full : aead.gcm.TagLength
| Truncated120 : aead.gcm.TagLength
| Truncated112 : aead.gcm.TagLength
| Truncated104 : aead.gcm.TagLength
| Truncated96 : aead.gcm.TagLength
| Truncated64 : aead.gcm.TagLength
| Truncated32 : aead.gcm.TagLength

/-- `TagLength::bytes`. -/
def aead.gcm.TagLength.bytes (self : aead.gcm.TagLength) : Usize :=
  match self with
  | .Full => 16#usize
  | .Truncated120 => 15#usize
  | .Truncated112 => 14#usize
  | .Truncated104 => 13#usize
  | .Truncated96 => 12#usize
  | .Truncated64 => 8#usize
  | .Truncated32 => 4#usize

/-- `Iv`, whose bytes are the IV. -/
structure aead.gcm.Iv where
  bytes : Slice U8

/-- `Key`, whose `ManuallyDrop<super::Key>` is an `aead::Key`. Its `tag_len`
field is `tag_length`, since the method `tag_len` takes that name. -/
structure aead.gcm.Key where
  key : aead.Key
  tag_length : aead.gcm.TagLength

/-- `Tag`, whose first `len` bytes are the tag. -/
structure aead.gcm.Tag where
  bytes : Std.Array U8 16#usize
  len : Usize

/-- `Key::tag_len`. -/
def aead.gcm.Key.tag_len (self : aead.gcm.Key) : Usize :=
  self.tag_length.bytes

/-- `Tag::as_ref`: the first `len` bytes of the tag. -/
def aead.gcm.Tag.as_ref (self : aead.gcm.Tag) : Slice U8 :=
  Slice.from (self.bytes.val.take self.len.val) (by
    have := self.bytes.property; simp only [List.length_take] at *; scalar_tac)

/-- `Key::new`: the `aead::Key` for the algorithm's key length, refused only
for a key of another length, and the tag length. -/
def aead.gcm.Key.new (algorithm : cipher.Algorithm) (key : Slice U8) (tag_len : aead.gcm.TagLength) :
    Result (core.result.Result aead.gcm.Key error.Error) :=
  let alg := if algorithm.key_len = 16#usize then aead.AES_128_GCM
    else if algorithm.key_len = 24#usize then aead.AES_192_GCM else aead.AES_256_GCM
  if key.len ≠ algorithm.key_len then ok (.Err .WrongLength)
  else do
    let r ← aead.Key.new alg key
    match r with
    | .Err e => ok (.Err e)
    | .Ok k => ok (.Ok { key := k, tag_length := tag_len })

/-- The arm of `seal_in_place_separate_tag` for an IV that is not 12 bytes,
which runs `encrypt_any`. Opaque: rind's by-8 path, which no proof covers. -/
opaque aead.gcm.Key.seal_other_iv (self : aead.gcm.Key) (iv : aead.gcm.Iv) (aad in_out : Slice U8) :
    Result ((core.result.Result aead.gcm.Tag error.Error) × Slice U8)

/-- `Key::seal_in_place_separate_tag`: for a 12-byte IV, `aead::Key`'s seal
under the IV as its nonce, with the tag of the key's length. -/
def aead.gcm.Key.seal_in_place_separate_tag (self : aead.gcm.Key) (iv : aead.gcm.Iv) (aad in_out : Slice U8) :
    Result ((core.result.Result aead.gcm.Tag error.Error) × Slice U8) := do
  let r ← core.array.TryFromSharedArraySlice.try_from 12#usize iv.bytes
  match r with
  | .Ok nonce =>
    let (r, in_out) ← aead.Key.seal_in_place_separate_tag self.key
      (aead.Nonce.assume_unique_for_key nonce) aad in_out
    match r with
    | .Ok tag => ok (.Ok ⟨tag.bytes, aead.gcm.Key.tag_len self⟩, in_out)
    | .Err e => ok (.Err e, in_out)
  | .Err _ => aead.gcm.Key.seal_other_iv self iv aad in_out

/-- `Key::seal_in_place_append_tag`: seals the buffer's `as_mut` view, then
hands the tag to its `extend`. -/
def aead.gcm.Key.seal_in_place_append_tag {InOut : Type}
    (AsMutInst : core.convert.AsMut InOut (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend InOut U8) (self : aead.gcm.Key) (iv : aead.gcm.Iv)
    (aad : Slice U8) (in_out : InOut) : Result ((core.result.Result Unit error.Error) × InOut) := do
  let (view, back) ← AsMutInst.as_mut in_out
  let (r, view) ← aead.gcm.Key.seal_in_place_separate_tag self iv aad view
  let in_out := back view
  match r with
  | .Ok tag =>
    let in_out ← ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8)
      in_out (aead.gcm.Tag.as_ref tag)
    ok (.Ok (), in_out)
  | .Err e => ok (.Err e, in_out)

/-- The arm of `open` for an IV that is not 12 bytes or a tag that is not 16,
which runs `decrypt_any`. Opaque: rind's by-8 path, which no proof covers. -/
opaque aead.gcm.Key.open_other (self : aead.gcm.Key) (iv : aead.gcm.Iv) (aad tag in_out : Slice U8) :
    Result ((core.result.Result Unit error.Error) × Slice U8)

/-- `Key::open`: for a 12-byte IV and a 16-byte tag, `aead::Key`'s open. -/
def aead.gcm.Key.open (self : aead.gcm.Key) (iv : aead.gcm.Iv) (aad tag in_out : Slice U8) :
    Result ((core.result.Result Unit error.Error) × Slice U8) := do
  let r ← core.array.TryFromSharedArraySlice.try_from 12#usize iv.bytes
  match r with
  | .Ok nonce =>
    let r ← core.array.TryFromSharedArraySlice.try_from 16#usize tag
    match r with
    | .Ok tag16 =>
      let (r, in_out) ← aead.Key.open_in_place_separate_tag self.key
        (aead.Nonce.assume_unique_for_key nonce) aad ⟨tag16⟩ in_out
      match r with
      | .Ok _ => ok (.Ok (), in_out)
      | .Err e => ok (.Err e, in_out)
    | .Err _ => aead.gcm.Key.open_other self iv aad tag in_out
  | .Err _ => aead.gcm.Key.open_other self iv aad tag in_out

/-- `Key::open_in_place_separate_tag`: refused unless the tag is the key's
length, and otherwise `open`. -/
def aead.gcm.Key.open_in_place_separate_tag (self : aead.gcm.Key) (iv : aead.gcm.Iv)
    (aad tag in_out : Slice U8) : Result ((core.result.Result (Slice U8) error.Error) × Slice U8) := do
  if tag.len ≠ aead.gcm.Key.tag_len self then ok (.Err .WrongLength, in_out)
  else
    let (r, out) ← aead.gcm.Key.open self iv aad tag in_out
    match r with
    | .Ok () => ok (.Ok out, out)
    | .Err e => ok (.Err e, out)

/-- `Key::open_in_place`: the tag is the key's length at the end of `in_out`,
refused if `in_out` is shorter. Returns the bytes before the tag, which it opens
in place. -/
def aead.gcm.Key.open_in_place (self : aead.gcm.Key) (iv : aead.gcm.Iv) (aad in_out : Slice U8) :
    Result ((core.result.Result (Slice U8) error.Error) × Slice U8) :=
  if in_out.length < (aead.gcm.Key.tag_len self).val then ok (.Err .DecryptFailed, in_out)
  else do
    let split := in_out.length - (aead.gcm.Key.tag_len self).val
    let body := Slice.from (in_out.val.take split) (by
      have := in_out.property; simp only [List.length_take]; omega)
    let tag := Slice.from (in_out.val.drop split) (by
      have := in_out.property; simp only [List.length_drop]; omega)
    let (r, body) ← aead.gcm.Key.open self iv aad tag body
    match r with
    | .Ok () => ok (.Ok body, body)
    | .Err e => ok (.Err e, body)

/-! ## The glue -/

/-- `try_into` of a slice of length `N` to an array holds the slice's bytes. -/
theorem try_from_len (N : Usize) (s : Slice U8) (h : s.length = N.val) :
    ∃ a : Std.Array U8 N, core.array.TryFromSharedArraySlice.try_from N s = ok (.Ok a) ∧
      a.val = s.val := by
  have hs : s.len = N := by scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dite_eq_left hs]
  refine ⟨_, rfl, ?_⟩
  simp [Std.Array.from_val]

/-- `Key::new` for AES-128 or AES-256: a key of the algorithm's length holds
AES-GCM on Vale's tier, and any other length is refused. -/
theorem gcm_key_new (h : RunsValeAesGcm) (algorithm : cipher.Algorithm) (alg : Algorithm)
    (halg : (algorithm.key_len = 16#usize ∧ alg = .AES_128) ∨
      (algorithm.key_len = 32#usize ∧ alg = .AES_256))
    (tag_len : aead.gcm.TagLength) (key : Slice U8) :
    aead.gcm.Key.new algorithm key tag_len ⦃ r =>
      if key.length = algorithm.key_len.val then
        ∃ k, r = .Ok k ∧ k.tag_length = tag_len ∧ KeyReady alg (bvs key.val) k.key
      else r = .Err .WrongLength ⦄ := by
  have hv := Slice.len_val key
  unfold aead.gcm.Key.new
  dsimp only
  rcases halg with ⟨h16, rfl⟩ | ⟨h32, rfl⟩
  · rw [ite_eq_left h16, h16]
    by_cases hl : key.length = 16
    · have hu : key.len = 16#usize := by scalar_tac
      rw [ite_eq_right (not_not.mpr hu)]
      apply WP.spec_bind (aes_gcm_new h .AES_128 aead.AES_128_GCM (Or.inl ⟨rfl, rfl⟩) key)
      rintro r hr
      have hn : key.length = 4 * nk .AES_128 := by rw [hl]; rfl
      rw [ite_eq_left hn] at hr
      obtain ⟨k, rfl, hkr⟩ := hr
      exact (WP.spec_ok _).2 (by
        rw [ite_eq_left (show key.length = (16#usize).val from hl)]
        exact ⟨_, rfl, rfl, hkr⟩)
    · have hu : key.len ≠ 16#usize := by scalar_tac
      rw [ite_eq_left hu]
      exact (WP.spec_ok _).2 (by simp [hl])
  · have h16' : ¬ algorithm.key_len = 16#usize := by scalar_tac
    have h24' : ¬ algorithm.key_len = 24#usize := by scalar_tac
    rw [ite_eq_right h16', ite_eq_right h24', h32]
    by_cases hl : key.length = 32
    · have hu : key.len = 32#usize := by scalar_tac
      rw [ite_eq_right (not_not.mpr hu)]
      apply WP.spec_bind (aes_gcm_new h .AES_256 aead.AES_256_GCM (Or.inr ⟨rfl, rfl⟩) key)
      rintro r hr
      have hn : key.length = 4 * nk .AES_256 := by rw [hl]; rfl
      rw [ite_eq_left hn] at hr
      obtain ⟨k, rfl, hkr⟩ := hr
      exact (WP.spec_ok _).2 (by
        rw [ite_eq_left (show key.length = (32#usize).val from hl)]
        exact ⟨_, rfl, rfl, hkr⟩)
    · have hu : key.len ≠ 32#usize := by scalar_tac
      rw [ite_eq_left hu]
      exact (WP.spec_ok _).2 (by simp [hl])

/-- Sealing with a 12-byte IV on a key whose tags are full: the ciphertext in
place and the 16-byte tag are AES-GCM's, for AAD and messages under 2^32 bytes
and messages of 129 bytes and more. -/
theorem gcm_key_seal (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.gcm.Key) (hk : KeyReady alg key k.key)
    (htag : k.tag_length = .Full) (iv : aead.gcm.Iv) (hiv : iv.bytes.length = 12)
    (aad in_out : Slice U8) (haad : aad.length < 2 ^ 32) (hin : in_out.length < 2 ^ 32)
    (hlong : 129 ≤ in_out.length) :
    k.seal_in_place_separate_tag iv aad in_out ⦃ r =>
      ∃ tag, r.1 = .Ok tag ∧ tag.len = 16#usize ∧ r.2.length = in_out.length ∧
        (bvs r.2.val, bvs tag.bytes.val) =
          gcmEncrypt alg key (bvs iv.bytes.val) (bvs in_out.val) (bvs aad.val) ⦄ := by
  obtain ⟨a, ha, hav⟩ := try_from_len 12#usize iv.bytes hiv
  unfold aead.gcm.Key.seal_in_place_separate_tag
  simp only [ha, bind_ok]
  apply WP.spec_bind (aes_gcm_seal he alg key k.key hk ⟨a⟩ aad in_out haad hin hlong)
  rintro ⟨r, out⟩ ⟨tag, hr, hlen, henc⟩
  simp only at hr hlen henc
  subst hr
  have htl : aead.gcm.Key.tag_len k = 16#usize := by
    simp [aead.gcm.Key.tag_len, aead.gcm.TagLength.bytes, htag]
  simp only [htl, hav] at henc ⊢
  exact (WP.spec_ok _).2 ⟨⟨tag.bytes, 16#usize⟩, rfl, rfl, hlen, henc⟩

/-- A full tag's `as_ref` is its 16 bytes, which `to_slice` gives. -/
theorem tag_as_ref_full (t : aead.gcm.Tag) (h : t.len = 16#usize) :
    aead.gcm.Tag.as_ref t = t.bytes.to_slice := by
  apply Slice.ext
  have hl : t.len.val = 16 := by rw [h]; rfl
  simp only [aead.gcm.Tag.as_ref, Std.Array.to_slice, hl, Slice.from_val]
  have := t.bytes.property
  rw [List.take_of_length_le (by simp [this])]

/-- Sealing through any buffer `InOut` with a 12-byte IV on a full-tag key: as
`aes_gcm_seal_append_tag`, the call returns what its `extend` makes of the
view's ciphertext and the 16-byte tag. -/
theorem gcm_key_seal_append_tag (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.gcm.Key) (hk : KeyReady alg key k.key)
    (htag : k.tag_length = .Full) (iv : aead.gcm.Iv) (hiv : iv.bytes.length = 12) (aad : Slice U8)
    {InOut : Type} (AsMutInst : core.convert.AsMut InOut (Slice U8))
    (ExtendInst : core.iter.traits.collect.Extend InOut U8) (in_out : InOut) (view : Slice U8)
    (back : Slice U8 → InOut) (hview : AsMutInst.as_mut in_out = ok (view, back))
    (haad : aad.length < 2 ^ 32) (hin : view.length < 2 ^ 32) (hlong : 129 ≤ view.length)
    (Q : (core.result.Result Unit error.Error) × InOut → Prop)
    (hext : ∀ (ct : Slice U8) (tag : Std.Array U8 16#usize), ct.length = view.length →
      (bvs ct.val, bvs tag.val) = gcmEncrypt alg key (bvs iv.bytes.val) (bvs view.val) (bvs aad.val) →
      ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8) (back ct)
        tag.to_slice ⦃ out => Q (.Ok (), out) ⦄) :
    k.seal_in_place_append_tag AsMutInst ExtendInst iv aad in_out ⦃ Q ⦄ := by
  unfold aead.gcm.Key.seal_in_place_append_tag
  simp only [hview, bind_ok]
  apply WP.spec_bind (gcm_key_seal he alg key k hk htag iv hiv aad view haad hin hlong)
  rintro ⟨r, ct⟩ ⟨tag, hr, htl, hlen, henc⟩
  simp only at hr hlen henc
  rw [hr]
  show (do
      let in_out ← ExtendInst.extend (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U8)
        (back ct) (aead.gcm.Tag.as_ref tag)
      ok (.Ok (), in_out) : Result (core.result.Result Unit error.Error × InOut)) ⦃ Q ⦄
  rw [tag_as_ref_full tag htl]
  exact WP.spec_bind (hext ct tag.bytes hlen henc) fun out h => (WP.spec_ok _).2 h

/-- `Key::open` for a 12-byte IV and a 16-byte tag: as `aes_gcm_open_separate_tag`,
it succeeds exactly when AES-GCM's tag verifies, and otherwise fails, leaving zeros. -/
theorem gcm_key_open_chain (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.gcm.Key) (hk : KeyReady alg key k.key)
    (iv : aead.gcm.Iv) (hiv : iv.bytes.length = 12) (aad tag in_out : Slice U8)
    (htl : tag.length = 16) (haad : aad.length < 2 ^ 32) (hin : in_out.length < 2 ^ 32) :
    k.open iv aad tag in_out ⦃ r =>
      let out := gcmDecrypt alg key (bvs iv.bytes.val) (bvs in_out.val) (bvs aad.val) (bvs tag.val)
      if out.2 then r.1 = .Ok () ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate in_out.length 0#u8 ⦄ := by
  obtain ⟨a, ha, hav⟩ := try_from_len 16#usize tag htl
  obtain ⟨n, hn, hnv⟩ := try_from_len 12#usize iv.bytes hiv
  unfold aead.gcm.Key.open
  simp only [hn, ha, bind_ok]
  apply WP.spec_bind (aes_gcm_open_separate_tag he alg key k.key hk ⟨n⟩ aad ⟨a⟩ in_out haad hin)
  rintro ⟨r', out'⟩ hr'
  simp only [hav, hnv] at hr'
  by_cases hc : (gcmDecrypt alg key (bvs iv.bytes.val) (bvs in_out.val) (bvs aad.val) (bvs tag.val)).2 = true
  · simp only [hc, ↓reduceIte] at hr'
    obtain ⟨rfl, hout⟩ := hr'
    refine (WP.spec_ok _).2 ?_
    simp only [hc, ↓reduceIte]
    exact ⟨trivial, hout⟩
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hr'
    obtain ⟨rfl, hout⟩ := hr'
    refine (WP.spec_ok _).2 ?_
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
    exact ⟨trivial, hout⟩

/-- `Key::open_in_place_separate_tag` for a 12-byte IV and a 16-byte tag: as
`aes_gcm_open_separate_tag`. -/
theorem gcm_key_open_separate_tag (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.gcm.Key) (hk : KeyReady alg key k.key)
    (htag : k.tag_length = .Full) (iv : aead.gcm.Iv) (hiv : iv.bytes.length = 12)
    (aad tag in_out : Slice U8) (htl : tag.length = 16) (haad : aad.length < 2 ^ 32)
    (hin : in_out.length < 2 ^ 32) :
    k.open_in_place_separate_tag iv aad tag in_out ⦃ r =>
      let out := gcmDecrypt alg key (bvs iv.bytes.val) (bvs in_out.val) (bvs aad.val) (bvs tag.val)
      if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate in_out.length 0#u8 ⦄ := by
  have htl' : aead.gcm.Key.tag_len k = 16#usize := by
    simp [aead.gcm.Key.tag_len, aead.gcm.TagLength.bytes, htag]
  have hlen : ¬ tag.len ≠ aead.gcm.Key.tag_len k := by
    rw [htl']
    have := Slice.len_val tag
    intro h
    scalar_tac
  unfold aead.gcm.Key.open_in_place_separate_tag
  rw [ite_eq_right hlen]
  apply WP.spec_bind (gcm_key_open_chain he alg key k hk iv hiv aad tag in_out htl haad hin)
  rintro ⟨r', out'⟩ hr'
  by_cases hc : (gcmDecrypt alg key (bvs iv.bytes.val) (bvs in_out.val) (bvs aad.val) (bvs tag.val)).2 = true
  · simp only [hc, ↓reduceIte] at hr'
    obtain ⟨rfl, hout⟩ := hr'
    refine (WP.spec_ok _).2 ?_
    simp only [hc, ↓reduceIte]
    exact ⟨trivial, hout⟩
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hr'
    obtain ⟨rfl, hout⟩ := hr'
    refine (WP.spec_ok _).2 ?_
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
    exact ⟨trivial, hout⟩

/-- `Key::open_in_place` for a 12-byte IV on a key whose tags are full: as
`aes_gcm_open`, it is refused if `in_out` is shorter than a tag, and otherwise
opens the bytes before the last 16, which must verify. -/
theorem gcm_key_open (he : ∃ e, low.entry.Entry.new_secret = ok e) (alg : Algorithm)
    (key : List (BitVec 8)) (k : aead.gcm.Key) (hk : KeyReady alg key k.key)
    (htag : k.tag_length = .Full) (iv : aead.gcm.Iv) (hiv : iv.bytes.length = 12)
    (aad in_out : Slice U8) (haad : aad.length < 2 ^ 32) (hin : in_out.length < 2 ^ 32) :
    k.open_in_place iv aad in_out ⦃ r =>
      if in_out.length < 16 then r.1 = .Err .DecryptFailed else
      let out := gcmDecrypt alg key (bvs iv.bytes.val) (bvs (in_out.val.take (in_out.length - 16)))
        (bvs aad.val) (bvs (in_out.val.drop (in_out.length - 16)))
      if out.2 then r.1 = .Ok r.2 ∧ bvs r.2.val = out.1
      else r.1 = .Err .DecryptFailed ∧ r.2.val = List.replicate (in_out.length - 16) 0#u8 ⦄ := by
  obtain ⟨kk, tl⟩ := k
  have htl' : tl = .Full := htag
  subst htl'
  unfold aead.gcm.Key.open_in_place
  have h16 : (16#usize).val = 16 := rfl
  simp only [aead.gcm.Key.tag_len, aead.gcm.TagLength.bytes, h16]
  by_cases h' : in_out.length < 16
  · simp only [h', ↓reduceIte]
    exact (WP.spec_ok _).2 (by simp)
  · have hl : in_out.val.length = in_out.length := rfl
    simp only [h', ↓reduceIte]
    have hb : (in_out.val.take (in_out.length - 16)).length ≤ Usize.max := by
      have := in_out.property; simp only [List.length_take]; scalar_tac
    have hd : (in_out.val.drop (in_out.length - 16)).length ≤ Usize.max := by
      have := in_out.property; simp only [List.length_drop]; scalar_tac
    have hwt : (Slice.from (in_out.val.drop (in_out.length - 16)) hd).length = 16 := by
      simp only [Slice.length, Slice.from_val, List.length_drop]; omega
    have hwin : (Slice.from (in_out.val.take (in_out.length - 16)) hb).length < 2 ^ 32 := by
      simp only [Slice.length, Slice.from_val, List.length_take]; scalar_tac
    apply WP.spec_bind (gcm_key_open_chain he alg key ⟨kk, .Full⟩ hk iv hiv aad
      (Slice.from (in_out.val.drop (in_out.length - 16)) hd)
      (Slice.from (in_out.val.take (in_out.length - 16)) hb) hwt haad hwin)
    rintro ⟨r', out'⟩ hr'
    simp only [Slice.from_val] at hr' ⊢
    have hbl : (Slice.from (in_out.val.take (in_out.length - 16)) hb).length = in_out.length - 16 := by
      simp only [Slice.length, Slice.from_val, List.length_take]; omega
    by_cases hc : (gcmDecrypt alg key (bvs iv.bytes.val) (bvs (in_out.val.take (in_out.length - 16)))
        (bvs aad.val) (bvs (in_out.val.drop (in_out.length - 16)))).2 = true
    · simp only [hc, ↓reduceIte] at hr' ⊢
      obtain ⟨rfl, hout⟩ := hr'
      refine (WP.spec_ok _).2 ?_
      exact ⟨rfl, hout⟩
    · simp only [hc, ↓reduceIte, Bool.false_eq_true, hbl] at hr' ⊢
      obtain ⟨rfl, hout⟩ := hr'
      refine (WP.spec_ok _).2 ?_
      exact ⟨rfl, hout⟩

end rind.x86_64
