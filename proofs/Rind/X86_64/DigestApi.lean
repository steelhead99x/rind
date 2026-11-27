import Rind.X86_64.Hmac
import Rind.X86_64.DigestDispatch
open Aeneas Aeneas.Std Result rind.spec

/-!
# The digest API, `high::digest`, through the modelled dispatch

`digest` and `Context` compute FIPS 180-4's SHA-1 and SHA-256, through the
dispatch `Rind.X86_64.DigestDispatch` models, down to each hash's `HashSpec`;
`Rind.X86_64.Sha512` proves the SHA-512 family's. `CtxOf` says what a
`Context` has been given.
`admin/prove` writes the aarch64 proof from this file by renaming the target.
-/

namespace rind.x86_64

/-! ## Over any hash meeting `HashSpec` -/

section
variable {Self C S : Type} {inst : high.hash.Hash Self C S} {H : List Byte → List Byte}
  {B L max : Nat} {Abs : List U8 → S → Prop} {CAbs : List U8 → C → Prop}

theorem hashing_update_spec (hs : HashSpec inst H B L max Abs CAbs)
    (V : high.digest.Variant C) (hV : V.hashHashContextInst = inst.HashContextInst)
    (p : List U8) (h : high.digest.Hashing C) (hc : CAbs p h.context) (data : Slice U8)
    (hl : p.length + data.length ≤ max) :
    high.digest.Hashing.update V h data ⦃ h' => CAbs (p ++ data.val) h'.context ⦄ := by
  unfold high.digest.Hashing.update
  rw [hV]
  step with hs.update p _ data hc hl as ⟨c, hc'⟩
  exact hc'

theorem hashing_finish_spec (hs : HashSpec inst H B L max Abs CAbs)
    (V : high.digest.Variant C) (hV : V.hashHashContextInst = inst.HashContextInst)
    (p : List U8) (h : high.digest.Hashing C) (hc : CAbs p h.context) (hl : p.length ≤ max) :
    high.digest.Hashing.finish V h ⦃ d => outLen d.algorithm = L ∧ digestBytes d = H (bv p) ⦄ := by
  unfold high.digest.Hashing.finish
  rw [hV]
  exact hs.finish p _ hc hl

/-- `Hashing::<C>::start`, for a variant `V` whose `state` wraps a `Hashing` as
`S` does, and whose `hashing` unwraps it. -/
theorem hashing_start_spec (hs : HashSpec inst H B L max Abs CAbs)
    (V : high.digest.Variant C) (hV : V.hashHashContextInst = inst.HashContextInst)
    (hnew : V.NEW ⦃ c => CAbs [] c ⦄) (S : high.digest.Hashing C → high.digest.State)
    (hstate : ∀ h, V.state h = ok (S h))
    (hhash : ∀ h, ∃ back, V.hashing (S h) = ok (some h, back) ∧ ∀ h', back (some h') = S h')
    (st : high.digest.State) (data : Slice U8) (hl : data.length ≤ max)
    (P : high.digest.State → Prop) (hP : ∀ h : high.digest.Hashing C, CAbs data.val h.context → P (S h)) :
    high.digest.Hashing.start V st data ⦃ P ⦄ := by
  unfold high.digest.Hashing.start
  rw [hV]
  step with hnew as ⟨c, hc⟩
  obtain ⟨back, hb1, hb2⟩ := hhash { context := c, ops := () }
  simp only [hstate, hb1, bind_ok]
  step with hs.update [] _ data hc (by simpa using hl) as ⟨c', hc'⟩
  simpa [hb2] using hP _ (by simpa using hc')

end

/-! ## Each variant's fresh context -/

theorem sha1_variant_new_spec :
    high.hash.Sha1Context.Insts.RindHighDigestVariant.NEW ⦃ c => Sha1Ctx [] c ⦄ := by
  unfold high.hash.Sha1Context.Insts.RindHighDigestVariant.NEW mid.sha1.Sha1Context.new
  step with sha1_new_spec as ⟨s, hs⟩
  step with sha1_resume_spec [] s hs as ⟨c, hc⟩
  exact hc

theorem sha256_variant_new_spec :
    high.hash.Sha256Context.Insts.RindHighDigestVariant.NEW ⦃ c => Sha256Ctx [] c ⦄ := by
  unfold high.hash.Sha256Context.Insts.RindHighDigestVariant.NEW mid.sha2.Sha256Context.new
  step with sha256_new_spec as ⟨s, hs⟩
  step with sha256_resume_spec [] s hs as ⟨c, hc⟩
  exact hc

/-! ## The API -/

/-- The hash each algorithm proven here runs, over spec bytes. -/
def digestHash : high.digest.Algorithm → List Byte → List Byte
  | .SHA1 => sha1.hash
  | _ => sha256.hash

/-- What `a`'s hash assumes of its block functions. -/
def ShaBlocksOf : high.digest.Algorithm → Prop
  | .SHA1 => Sha1Blocks
  | .SHA256 => Sha256Blocks
  | _ => True

/-- What the digest API under `a` needs: `a` is SHA-1 or SHA-256, the entry
guard passes, and its block functions meet their contracts. -/
def RunsDigest (a : high.digest.Algorithm) : Prop :=
  (a = .SHA1 ∨ a = .SHA256) ∧ (∃ e, low.entry.Entry.new_secret = ok e) ∧ ShaBlocksOf a

/-- `s` is the state of a `Context` of `a` that has been given `p`. -/
def StateOf (a : high.digest.Algorithm) (p : List U8) : high.digest.State → Prop
  | .Fresh => p = []
  | .Sha1 h => a = .SHA1 ∧ Sha1Ctx p h.context
  | .Sha256 h => a = .SHA256 ∧ Sha256Ctx p h.context
  | _ => False

/-- `c` is a `Context` of `a` that has been given `p`. -/
def CtxOf (a : high.digest.Algorithm) (p : List U8) (c : high.digest.Context) : Prop :=
  c.algorithm = a ∧ StateOf a p c.state

/-- `digest::digest`. -/
theorem digest_spec (a : high.digest.Algorithm) (hr : RunsDigest a) (data : Slice U8)
    (hl : data.length ≤ maxInput) :
    high.digest.digest a data ⦃ d =>
      outLen d.algorithm = outLen a ∧ digestBytes d = digestHash a (bv data.val) ⦄ := by
  obtain ⟨ha, ⟨e, he⟩, hb⟩ := hr
  unfold high.digest.digest
  rw [he, bind_ok]
  rcases ha with rfl | rfl
  · simp only [high.digest.Algorithm.hash]
    rw [← (sha1_hashSpec hb).hash_default]
    exact (sha1_hashSpec hb).hash_spec data hl
  · simp only [high.digest.Algorithm.hash]
    rw [← (sha256_hashSpec hb).hash_default]
    exact (sha256_hashSpec hb).hash_spec data hl

/-- `Context::new`. -/
theorem digest_ctx_new_spec (a : high.digest.Algorithm) :
    high.digest.Context.new a ⦃ c => CtxOf a [] c ⦄ := by
  simp [high.digest.Context.new, CtxOf, StateOf, WP.spec_ok]

/-- `Context::update`. -/
theorem digest_ctx_update_spec (a : high.digest.Algorithm) (hr : RunsDigest a) (p : List U8)
    (c : high.digest.Context) (hc : CtxOf a p c) (data : Slice U8)
    (hl : p.length + data.length ≤ maxInput) :
    high.digest.Context.update c data ⦃ c' => CtxOf a (p ++ data.val) c' ⦄ := by
  have hb := hr.2.2
  obtain ⟨a', s⟩ := c
  obtain ⟨rfl, hc⟩ := hc
  unfold high.digest.Context.update high.digest.State.update
  rcases s with _ | h | h | h | h | h | h | h | h | h <;> simp only [StateOf] at hc
  · subst hc
    rcases hr.1 with rfl | rfl <;> simp only [high.digest.Algorithm.start]
    · step with hashing_start_spec (sha1_hashSpec hb)
        high.hash.Sha1Context.Insts.RindHighDigestVariant rfl sha1_variant_new_spec .Sha1
        (fun _ => rfl) (fun _ => ⟨_, rfl, fun _ => rfl⟩) _ data (by simpa using hl)
        (fun st => CtxOf .SHA1 data.val { algorithm := .SHA1, state := st })
        (fun h hh => by simpa [CtxOf, StateOf] using hh) as ⟨st, hst⟩
      simpa [CtxOf] using hst
    · step with hashing_start_spec (sha256_hashSpec hb)
        high.hash.Sha256Context.Insts.RindHighDigestVariant rfl sha256_variant_new_spec .Sha256
        (fun _ => rfl) (fun _ => ⟨_, rfl, fun _ => rfl⟩) _ data (by simpa using hl)
        (fun st => CtxOf .SHA256 data.val { algorithm := .SHA256, state := st })
        (fun h hh => by simpa [CtxOf, StateOf] using hh) as ⟨st, hst⟩
      simpa [CtxOf] using hst
  all_goals obtain ⟨rfl, hc⟩ := hc
  · step with hashing_update_spec (sha1_hashSpec hb)
      high.hash.Sha1Context.Insts.RindHighDigestVariant rfl p _ hc data hl as ⟨h', hh⟩
    exact ⟨rfl, rfl, hh⟩
  · step with hashing_update_spec (sha256_hashSpec hb)
      high.hash.Sha256Context.Insts.RindHighDigestVariant rfl p _ hc data hl as ⟨h', hh⟩
    exact ⟨rfl, rfl, hh⟩

/-- `Context::finish`, which leaves the context fresh. -/
theorem digest_ctx_finish_spec (a : high.digest.Algorithm) (hr : RunsDigest a) (p : List U8)
    (c : high.digest.Context) (hc : CtxOf a p c) (hl : p.length ≤ maxInput) :
    high.digest.Context.finish c ⦃ r =>
      outLen r.1.algorithm = outLen a ∧ digestBytes r.1 = digestHash a (bv p) ∧
        CtxOf a [] r.2 ⦄ := by
  obtain ⟨a', s⟩ := c
  obtain ⟨rfl, hc⟩ := hc
  rcases s with _ | h | h | h | h | h | h | h | h | h <;> simp only [StateOf] at hc
  · subst hc
    apply high.digest.Context.finish_fresh
    apply WP.spec_mono (digest_spec a' hr _ (by simp [Slice.length]))
    rintro d ⟨h1, h2⟩
    exact ⟨h1, by simpa using h2, rfl, rfl⟩
  all_goals obtain ⟨rfl, hc⟩ := hc
  all_goals
    obtain ⟨-, ⟨e, he⟩, hb⟩ := hr
    unfold high.digest.Context.finish high.digest.State.finish
    rw [he, bind_ok]
  · step with hashing_finish_spec (sha1_hashSpec hb)
      high.hash.Sha1Context.Insts.RindHighDigestVariant rfl p _ hc hl as ⟨d, h1, h2⟩
    exact ⟨h1, h2, rfl, rfl⟩
  · step with hashing_finish_spec (sha256_hashSpec hb)
      high.hash.Sha256Context.Insts.RindHighDigestVariant rfl p _ hc hl as ⟨d, h1, h2⟩
    exact ⟨h1, h2, rfl, rfl⟩

end rind.x86_64
