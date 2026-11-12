import Rind.X86_64.Hmac
import Rind.X86_64.Sha512
import Rind.X86_64.CtEqual
open Aeneas Aeneas.Std Result rind.spec

/-!
# HMAC's API, `high::hmac`, through the modelled dispatch

`Key::new`, `sign`, `verify`, `Key::tag`, and `Context` compute RFC 2104's
HMAC over SHA-1, SHA-256, SHA-384, and SHA-512, through the dispatch
`Rind.X86_64.HmacDispatch` models, down to `Rind.X86_64.Hmac`'s proofs over
any hash. `KeyOf` says which key a `Key` holds and `StreamOf` what a
`Context` has been given. `admin/prove` writes the aarch64 proof from this
file by renaming the target.
-/

namespace rind.x86_64

/-- The hash each HMAC algorithm runs, over spec bytes. -/
def hmacHash : high.hmac.Algorithm → List Byte → List Byte
  | .HMAC_SHA1 => sha1.hash
  | .HMAC_SHA256 => sha256.hash
  | .HMAC_SHA384 => sha384Bytes
  | .HMAC_SHA512 => sha512Bytes

/-- The block length of each HMAC algorithm's hash. -/
def hmacBlock : high.hmac.Algorithm → Nat
  | .HMAC_SHA1 | .HMAC_SHA256 => 64
  | .HMAC_SHA384 | .HMAC_SHA512 => 128

/-- The tag length of each HMAC algorithm. -/
def tagLen : high.hmac.Algorithm → Nat
  | .HMAC_SHA1 => 20
  | .HMAC_SHA256 => 32
  | .HMAC_SHA384 => 48
  | .HMAC_SHA512 => 64

/-- RFC 2104's HMAC under `a`'s hash. -/
def hmacOf (a : high.hmac.Algorithm) (key text : List Byte) : List Byte :=
  hmac (hmacHash a) (hmacBlock a) key text

/-- What HMAC under `a` needs: the entry guard passes, and the CPU runs the
hash's routines (`Sha1Blocks` for SHA-1, `Sha256Blocks` for SHA-256, and
`RunsSha512` for SHA-384 and SHA-512). -/
def RunsHmac (a : high.hmac.Algorithm) : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧
    match a with
    | .HMAC_SHA1 => Sha1Blocks
    | .HMAC_SHA256 => Sha256Blocks
    | .HMAC_SHA384 | .HMAC_SHA512 => RunsSha512

/-- `k` is the key `Key::new(a, key)` makes. -/
def KeyOf (a : high.hmac.Algorithm) (key : List Byte) : high.hmac.Key → Prop
  | .Sha1 k => a = .HMAC_SHA1 ∧ HmacKeyed Sha1Absorbed sha1.hash 64 key k
  | .Sha256 k => a = .HMAC_SHA256 ∧ HmacKeyed Sha256Absorbed sha256.hash 64 key k
  | .Sha384 k => a = .HMAC_SHA384 ∧ HmacKeyed (Sha512Absorbed sha384Iv) sha384Bytes 128 key k
  | .Sha512 k => a = .HMAC_SHA512 ∧ HmacKeyed (Sha512Absorbed sha512Iv) sha512Bytes 128 key k

/-- `s` is a tag computation under `a` and `key` that has been given `p`. -/
def StreamOf (a : high.hmac.Algorithm) (key : List Byte) (p : List U8) :
    high.hmac.Streaming → Prop
  | .Sha1 h => a = .HMAC_SHA1 ∧ HmacCtx Sha1Ctx Sha1Absorbed sha1.hash 64 key p h
  | .Sha256 h => a = .HMAC_SHA256 ∧ HmacCtx Sha256Ctx Sha256Absorbed sha256.hash 64 key p h
  | .Sha384 h => a = .HMAC_SHA384 ∧ HmacCtx (fun p c => Hashed sha384Iv c.inner p)
      (Sha512Absorbed sha384Iv) sha384Bytes 128 key p h
  | .Sha512 h => a = .HMAC_SHA512 ∧ HmacCtx (fun p c => Hashed sha512Iv c p)
      (Sha512Absorbed sha512Iv) sha512Bytes 128 key p h

theorem tagLen_eq (a : high.hmac.Algorithm) : ∃ n, a.tag_len = ok n ∧ n.val = tagLen a := by
  cases a <;> exact ⟨_, rfl, rfl⟩

/-- A bind into `ok`, as each dispatch arm wraps its result. -/
theorem spec_bind_ok {α β : Type} {m : Result α} {P : α → Prop} {f : α → β} {Q : β → Prop}
    (h : m ⦃ P ⦄) (hf : ∀ x, P x → Q (f x)) : (do let x ← m; ok (f x)) ⦃ Q ⦄ := by
  apply WP.spec_bind h
  intro x hx
  simp only [WP.spec_ok]
  exact hf x hx

theorem tagLen_le (a : high.hmac.Algorithm) : tagLen a ≤ hmacBlock a := by
  cases a <;> decide

theorem tagLen_pos (a : high.hmac.Algorithm) : 0 < tagLen a := by
  cases a <;> decide

theorem hmacOf_length (a : high.hmac.Algorithm) (key text : List Byte) :
    (RunsHmac a) → (hmacOf a key text).length = tagLen a := by
  rintro ⟨-, hc⟩
  cases a
  · exact (sha1_hashSpec hc).out.2.2.2.2 _
  · exact (sha256_hashSpec hc).out.2.2.2.2 _
  · exact (sha384_hashSpec hc).out.2.2.2.2 _
  · exact (sha512_hashSpec hc).out.2.2.2.2 _

/-- `Key::new` keys HMAC under `a` with `key`. -/
theorem key_new_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : Slice U8)
    (hk : key.length ≤ maxInput) :
    high.hmac.Key.new a key ⦃ k => KeyOf a (bv key.val) k ⦄ := by
  obtain ⟨⟨e, he⟩, hc⟩ := hr
  unfold high.hmac.Key.new
  rw [he, bind_ok]
  cases a <;> simp only [high.hmac.Algorithm.key]
  · exact spec_bind_ok (hmac_key_new_spec (sha1_hashSpec hc) key hk) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_key_new_spec (sha256_hashSpec hc) key hk) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_key_new_spec (sha384_hashSpec hc) key hk) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_key_new_spec (sha512_hashSpec hc) key hk) fun _ h => ⟨rfl, h⟩

/-- `Key::algorithm` is the algorithm the key was made with. -/
theorem key_algorithm_eq {a : high.hmac.Algorithm} {key : List Byte} {k : high.hmac.Key}
    (hk : KeyOf a key k) : high.hmac.Key.algorithm k = ok a := by
  cases k <;> obtain ⟨rfl, -⟩ := hk <;> rfl

/-- `Key::tag` is HMAC of the message. -/
theorem key_tag_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a key k) (m : Slice U8)
    (hm : hmacBlock a + m.length ≤ maxInput) :
    high.hmac.Key.tag k m ⦃ d =>
      outLen d.algorithm = tagLen a ∧ digestBytes d = hmacOf a key (bv m.val) ⦄ := by
  obtain ⟨-, hc⟩ := hr
  unfold high.hmac.Key.tag
  cases k <;> obtain ⟨rfl, hk⟩ := hk <;> simp only [high.hmac.Keyed.sign]
  · exact hmac_sign_spec (sha1_hashSpec hc) key _ hk m hm
  · exact hmac_sign_spec (sha256_hashSpec hc) key _ hk m hm
  · exact hmac_sign_spec (sha384_hashSpec hc) key _ hk m hm
  · exact hmac_sign_spec (sha512_hashSpec hc) key _ hk m hm

/-- `sign` is HMAC of the message. -/
theorem sign_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a key k) (m : Slice U8)
    (hm : hmacBlock a + m.length ≤ maxInput) :
    high.hmac.sign k m ⦃ d =>
      outLen d.algorithm = tagLen a ∧ digestBytes d = hmacOf a key (bv m.val) ⦄ := by
  have := key_tag_spec a hr key k hk m hm
  obtain ⟨⟨e, he⟩, -⟩ := hr
  unfold high.hmac.sign
  rw [he, bind_ok]
  exact this

theorem bv_inj (x y : List U8) : bv x = bv y ↔ x = y := by
  constructor
  · intro h; rw [← ofBv_bv x, ← ofBv_bv y, h]
  · intro h; rw [h]

/-- Every hash's routines need the entry guard held, which `ct_equal` checks. -/
theorem RunsHmac.held {a : high.hmac.Algorithm} (hr : RunsHmac a) :
    low.entry.Entry.assert_held = ok () := by
  obtain ⟨-, h⟩ := hr
  cases a
  · exact h.held
  · exact h.held
  · exact h.2.1
  · exact h.2.1

/-- `verify` accepts exactly HMAC's tag of the message. -/
theorem verify_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a key k) (m t : Slice U8)
    (hm : hmacBlock a + m.length ≤ maxInput) :
    high.hmac.verify k m t ⦃ r =>
      r = if bv t.val = hmacOf a key (bv m.val) then .Ok () else .Err .BadSignature ⦄ := by
  have hs := key_tag_spec a hr key k hk m hm
  have hh := hr.held
  obtain ⟨⟨e, he⟩, -⟩ := hr
  unfold high.hmac.verify
  rw [he, bind_ok]
  unfold high.hmac.Key.tag at hs
  apply WP.spec_bind hs
  rintro d ⟨-, hd⟩
  unfold high.digest.Digest.ct_equal
  step with digest_as_ref_spec d as ⟨s, _, hsb⟩
  apply WP.spec_bind (ct_equal_spec hh s t)
  rintro _ rfl
  simp only [low.ct.into_public, bind_ok]
  have : (s.val = t.val) = (bv t.val = hmacOf a key (bv m.val)) := by
    rw [← hd, ← hsb, bv_inj]
    exact propext ⟨Eq.symm, Eq.symm⟩
  by_cases h : s.val = t.val
  · simp [h, ← this]
  · simp [h, ← this]

/-- `Key::start` and `Context::with_key` begin a tag computation. -/
theorem key_start_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a key k) :
    high.hmac.Key.start k ⦃ s => StreamOf a key [] s ⦄ := by
  obtain ⟨-, hc⟩ := hr
  unfold high.hmac.Key.start
  cases k <;> obtain ⟨rfl, hk⟩ := hk <;> simp only [high.hmac.Keyed.start]
  · exact spec_bind_ok (hmac_start_spec (sha1_hashSpec hc) key _ hk) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_start_spec (sha256_hashSpec hc) key _ hk) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_start_spec (sha384_hashSpec hc) key _ hk) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_start_spec (sha512_hashSpec hc) key _ hk) fun _ h => ⟨rfl, h⟩

theorem context_with_key_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a key k) :
    high.hmac.Context.with_key k ⦃ s => StreamOf a key [] s ⦄ :=
  key_start_spec a hr key k hk

/-- `Context::update` gives the computation more of the message. -/
theorem stream_update_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (p : List U8) (s : high.hmac.Streaming) (hs : StreamOf a key p s) (b : Slice U8)
    (hm : hmacBlock a + p.length + b.length ≤ maxInput) :
    high.hmac.Streaming.update s b ⦃ s' => StreamOf a key (p ++ b.val) s' ⦄ := by
  obtain ⟨-, hc⟩ := hr
  cases s <;> obtain ⟨rfl, hs⟩ := hs <;> simp only [high.hmac.Streaming.update]
  · exact spec_bind_ok (hmac_update_spec (sha1_hashSpec hc) key p _ _ hs b b rfl hm)
      fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_update_spec (sha256_hashSpec hc) key p _ _ hs b b rfl hm)
      fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_update_spec (sha384_hashSpec hc) key p _ _ hs b b rfl hm)
      fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_update_spec (sha512_hashSpec hc) key p _ _ hs b b rfl hm)
      fun _ h => ⟨rfl, h⟩

theorem context_update_spec' (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (p : List U8) (s : high.hmac.Context) (hs : StreamOf a key p s) (b : Slice U8)
    (hm : hmacBlock a + p.length + b.length ≤ maxInput) :
    high.hmac.Context.update s b ⦃ s' => StreamOf a key (p ++ b.val) s' ⦄ :=
  stream_update_spec a hr key p s hs b hm

/-- Finishing the computation is HMAC of what it was given. -/
theorem stream_finish_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (p : List U8) (s : high.hmac.Streaming) (hs : StreamOf a key p s)
    (hm : hmacBlock a + p.length ≤ maxInput) :
    high.hmac.Streaming.finish s ⦃ d =>
      outLen d.algorithm = tagLen a ∧ digestBytes d = hmacOf a key (bv p) ⦄ := by
  obtain ⟨-, hc⟩ := hr
  cases s <;> obtain ⟨rfl, hs⟩ := hs <;> simp only [high.hmac.Streaming.finish]
  · exact hmac_finish_spec (sha1_hashSpec hc) key p _ hs hm
  · exact hmac_finish_spec (sha256_hashSpec hc) key p _ hs hm
  · exact hmac_finish_spec (sha384_hashSpec hc) key p _ hs hm
  · exact hmac_finish_spec (sha512_hashSpec hc) key p _ hs hm

/-- `Context::sign` is HMAC of what the context was given. -/
theorem context_sign_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (p : List U8) (s : high.hmac.Context) (hs : StreamOf a key p s)
    (hm : hmacBlock a + p.length ≤ maxInput) :
    high.hmac.Context.sign s ⦃ d =>
      outLen d.algorithm = tagLen a ∧ digestBytes d = hmacOf a key (bv p) ⦄ := by
  have := stream_finish_spec a hr key p s hs hm
  obtain ⟨⟨e, he⟩, -⟩ := hr
  unfold high.hmac.Context.sign
  rw [he, bind_ok]
  exact this

/-- A cloned computation has been given the same message. -/
theorem stream_clone_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (p : List U8) (s : high.hmac.Streaming) (hs : StreamOf a key p s) :
    high.hmac.Streaming.Insts.CoreCloneClone.clone s ⦃ s' => StreamOf a key p s' ⦄ := by
  obtain ⟨-, hc⟩ := hr
  cases s <;> obtain ⟨rfl, hs⟩ := hs <;> simp only [high.hmac.Streaming.Insts.CoreCloneClone.clone]
  · exact spec_bind_ok (hmac_clone_spec (sha1_hashSpec hc) key p _ hs) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_clone_spec (sha256_hashSpec hc) key p _ hs) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_clone_spec (sha384_hashSpec hc) key p _ hs) fun _ h => ⟨rfl, h⟩
  · exact spec_bind_ok (hmac_clone_spec (sha512_hashSpec hc) key p _ hs) fun _ h => ⟨rfl, h⟩

/-- HMAC of `m` under `key` in one call: `sign(&Key::new(a, key), m)`. -/
theorem hmac_sign (a : high.hmac.Algorithm) (hr : RunsHmac a) (key m : Slice U8)
    (hk : key.length ≤ maxInput) (hm : hmacBlock a + m.length ≤ maxInput) :
    (do
      let k ← high.hmac.Key.new a key
      high.hmac.sign k m) ⦃ d => digestBytes d = hmacOf a (bv key.val) (bv m.val) ⦄ :=
  WP.spec_bind (key_new_spec a hr key hk) fun k hk' =>
    WP.spec_mono (sign_spec a hr _ k hk' m hm) fun _ h => h.2

end rind.x86_64
