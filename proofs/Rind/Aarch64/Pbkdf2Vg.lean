import Rind.Aarch64.Pbkdf2
import Rind.Aarch64.VgPbkdf2
open Aeneas Aeneas.Std Result rind.spec

/-!
# PBKDF2's API on pyca/verified-garbage's routines, aarch64 only

On aarch64 `Secret::new` keys a `Secret` for VG's routine, `mid::pbkdf2_vg`,
when the CPU has the instructions it runs, and for rind's loop otherwise.
This proves `Key::new` keeps the HMAC key, `Key::derive` writes RFC 8018's
PBKDF2 and `Key::verify` accepts exactly it, from `Rind.Aarch64.VgPbkdf2`'s
contracts of VG's routines, and `Secret` meets `Rind.Aarch64.Pbkdf2`'s
theorems on either branch: `secret_derive_spec` and `secret_verify_spec`.
The other targets translate no `mid::pbkdf2_vg`, so this file is aarch64's
own, not one `admin/prove` writes from x86_64's.

Beyond `Rind.Aarch64.Pbkdf2`'s premises, the theorems on VG's branch take the
iteration count to be positive, which its `NonZeroU32` holds and the
translation's `U32` forgets; `verify` takes that `zeroise`, which only wipes
its slice, returns. `secret_new_spec` also takes that the opaque CPU check
returns, whatever it finds, and proves the key `Secret::new` returns on
either branch, not which branch it picks.
-/

namespace rind.aarch64.kdf

/-! ## HMAC under a hashed key -/

/-- HMAC keyed by the hash of a key longer than a block is HMAC keyed by the
key, as RFC 2104 hashes such a key first. -/
theorem hmac_hashed_key (H : List Byte → List Byte) (B : Nat) (P : List Byte)
    (hP : B < P.length) (hH : (H P).length ≤ B) : hmac H B (H P) = hmac H B P := by
  funext text
  simp only [hmac, hH, ite_true, show ¬ P.length ≤ B by omega, ite_false]

/-- The HMAC key `Key::new` keeps of `P` under `a`: `P`, or its hash if
it is longer than a block. -/
def vgKeyBytes (a : high.hmac.Algorithm) (P : List Byte) : List Byte :=
  if P.length ≤ hmacBlock a then P else hmacHash a P

theorem hmacOf_vgKeyBytes (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte) :
    hmacOf a (vgKeyBytes a P) = hmacOf a P := by
  unfold vgKeyBytes
  split
  · rfl
  · rename_i h
    have hl : (hmacHash a P).length ≤ hmacBlock a := by
      obtain ⟨-, hc⟩ := hr
      cases a <;> simp only [hmacHash, hmacBlock] at hc ⊢
      · rw [(sha1_hashSpec hc).out.2.2.2.2]; decide
      · rw [(sha256_hashSpec hc).out.2.2.2.2]; decide
      · rw [(sha384_hashSpec hc).out.2.2.2.2]; decide
      · rw [(sha512_hashSpec hc).out.2.2.2.2]; decide
    unfold hmacOf
    rw [hmac_hashed_key _ _ _ (by omega) hl]

/-- PBKDF2 reads its password only through the pseudorandom function keyed
by it. -/
theorem pbkdf2_congr (prf : List Byte → List Byte → List Byte) (hLen : Nat) (P P' : List Byte)
    (h : prf P = prf P') (S : List Byte) (c L : Nat) :
    pbkdf2 prf hLen P S c L = pbkdf2 prf hLen P' S c L := by
  simp only [pbkdf2, h]

/-! ## `mid::pbkdf2_vg::Key` -/

/-- The `mid::pbkdf2_vg::Algorithm` of each HMAC algorithm. -/
def vgAlg : high.hmac.Algorithm → mid.pbkdf2_vg.Algorithm
  | .HMAC_SHA1 => .Sha1
  | .HMAC_SHA256 => .Sha256
  | .HMAC_SHA384 => .Sha384
  | .HMAC_SHA512 => .Sha512

/-- `key` is a `mid::pbkdf2_vg::Key` of the password `P` under `a`: it runs
`a`'s routine, and keeps `a`'s tag length and `P`'s HMAC key. -/
def VgKeyOf (a : high.hmac.Algorithm) (P : List Byte) (key : mid.pbkdf2_vg.Key) : Prop :=
  key.routine = vgHash a ∧ key.tag_len.val = tagLen a ∧ key.len.val ≤ 128 ∧
    bv (key.key.val.take key.len.val) = vgKeyBytes a P

/-- A length of at most `u32::MAX` blocks of `n` bytes is one of at most
`u32::MAX * n` bytes. -/
theorem ceilDiv_le_iff (len n : Nat) (hn : 0 < n) :
    (len + n - 1) / n ≤ U32.max ↔ len ≤ (2 ^ 32 - 1) * n := by
  have hm : U32.max = 2 ^ 32 - 1 := by simp [U32.max, U32.numBits]
  rw [hm, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hn, Nat.succ_mul, Nat.mul_comm]
  omega

/-- `check_len` accepts a length of at least one and at most `u32::MAX`
blocks, as `Rind::check_len` does. -/
theorem vg_check_len_spec (a : high.hmac.Algorithm) (P : List Byte) (key : mid.pbkdf2_vg.Key)
    (hk : VgKeyOf a P key) (len : Usize) :
    mid.pbkdf2_vg.Key.check_len key len ⦃ r =>
      r = if 0 < len.val ∧ (len.val + tagLen a - 1) / tagLen a ≤ U32.max then .Ok ()
        else .Err .WrongLength ⦄ := by
  have hpos := tagLen_pos a
  have hcast : (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = U32.max := by
    simp only [UScalar.cast_val_eq, core.num.U32.MAX]
    rcases System.Platform.numBits_eq with h | h <;> simp [h, U32.rMax, U32.max, U32.numBits]
  have hiff := ceilDiv_le_iff len.val (tagLen a) hpos
  have hm : U32.max = 2 ^ 32 - 1 := by simp [U32.max, U32.numBits]
  unfold mid.pbkdf2_vg.Key.check_len
  simp only [lift, bind_ok]
  have hmul := Usize.checked_mul_bv_spec key.tag_len (UScalar.cast UScalarTy.Usize core.num.U32.MAX)
  rw [hk.2.1, hcast, hm] at hmul
  have hlen : len.val ≤ Usize.max := by scalar_tac
  -- `too_long` is whether `len` exceeds `u32::MAX` tags.
  have htoo : core.option.Option.is_some_and
      mid.pbkdf2_vg.Key.check_len.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool
      (Usize.checked_mul key.tag_len (UScalar.cast UScalarTy.Usize core.num.U32.MAX)) len =
      ok (decide ((2 ^ 32 - 1) * tagLen a < len.val)) := by
    revert hmul
    cases Usize.checked_mul key.tag_len (UScalar.cast UScalarTy.Usize core.num.U32.MAX) with
    | none =>
      intro hmul
      simp only [core.option.Option.is_some_and]
      congr 1
      rw [eq_comm, decide_eq_false_iff_not]
      rw [Nat.mul_comm]
      omega
    | some z =>
      rintro ⟨-, hz, -⟩
      simp only [core.option.Option.is_some_and,
        mid.pbkdf2_vg.Key.check_len.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once,
        GT.gt, UScalar.lt_equiv, hz]
      rw [Nat.mul_comm]
  rw [htoo, bind_ok]
  by_cases h0 : len = 0#usize
  · subst h0
    simp
  · have hl0 : 0 < len.val := by
      rcases Nat.eq_zero_or_pos len.val with h | h
      · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) h0
      · exact h
    simp only [h0, ite_false, hl0, true_and, hiff]
    by_cases ht : (2 ^ 32 - 1) * tagLen a < len.val
    · simp only [ht, decide_true, ite_true, WP.spec_ok, show ¬ len.val ≤ (2 ^ 32 - 1) * tagLen a by omega,
        ite_false]
    · simp only [ht, decide_false, Bool.false_eq_true, ite_false, WP.spec_ok,
        show len.val ≤ (2 ^ 32 - 1) * tagLen a by omega, ite_true]

theorem key_bytes_spec (a : high.hmac.Algorithm) (P : List Byte) (key : mid.pbkdf2_vg.Key)
    (hk : VgKeyOf a P key) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice U8)) key.key { «end» := key.len } ⦃ s =>
      bv s.val = vgKeyBytes a P ⦄ := by
  rw [Array.index_SliceIndexRangeToUsizeSlice]
  apply WP.spec_mono (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec _ _
    (by simp [Array.to_slice, Slice.length]; exact hk.2.2.1))
  rintro s ⟨hs, -⟩
  rw [hs, ← hk.2.2.2]
  simp [List.slice, Array.to_slice]

/-- `Key::derive` writes PBKDF2's output, for an output of at least one and at
most `u32::MAX` blocks, and refuses any other, as `Rind::derive` does. -/
theorem vg_key_derive_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (key : mid.pbkdf2_vg.Key) (hk : VgKeyOf a P key)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (hi : 0 < iterations.val) (salt out : Slice U8) :
    mid.pbkdf2_vg.Key.derive key iterations salt out ⦃ r =>
      if 0 < out.length ∧ (out.length + tagLen a - 1) / tagLen a ≤ U32.max then
        r.1 = .Ok () ∧ r.2.length = out.length ∧
          bv r.2.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val out.length
      else r = (.Err .WrongLength, out) ⦄ := by
  have hpos := tagLen_pos a
  obtain ⟨e, he⟩ := hr.1
  unfold mid.pbkdf2_vg.Key.derive
  rw [he, bind_ok]
  apply WP.spec_bind (vg_check_len_spec a P key hk (Slice.len out))
  rintro c rfl
  rw [Slice.len_val]
  by_cases hc : 0 < out.length ∧ (out.length + tagLen a - 1) / tagLen a ≤ U32.max
  · simp only [hc, and_self, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      low.generic.zeroise.ZeroableRef.get]
    apply WP.spec_bind (key_bytes_spec a P key hk)
    intro s hs
    rw [hk.1]
    apply WP.spec_bind (vg_derive_spec a s salt iterations out hi
      ((ceilDiv_le_iff _ _ hpos).mp hc.2))
    rintro r ⟨hrl, hrb⟩
    simp only [WP.spec_ok]
    refine ⟨trivial, hrl, ?_⟩
    rw [hrb, hs]
    exact pbkdf2_congr _ _ _ _ (hmacOf_vgKeyBytes a hr P) _ _ _
  · simp only [hc, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp

/-- `zeroise` returns: it only wipes its slice. -/
def ZeroiseReturns : Prop :=
  ∀ s : Slice U8, ∃ s', low.generic.zeroise.zeroise U8.Insts.RindLowGenericZeroiseZeroable s = ok s'

/-- `Key::verify` accepts exactly PBKDF2's output, of at least the tag's
length and at most `u32::MAX` blocks, as `Rind::verify` does. -/
theorem vg_key_verify_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (hz : ZeroiseReturns)
    (P : List Byte) (key : mid.pbkdf2_vg.Key) (hk : VgKeyOf a P key)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (hi : 0 < iterations.val) (salt prev : Slice U8) :
    mid.pbkdf2_vg.Key.verify key iterations salt prev ⦃ r =>
      r = if prev.length < tagLen a ∨ ¬ (prev.length + tagLen a - 1) / tagLen a ≤ U32.max then
        .Err .WrongLength
      else if bv prev.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val
          prev.length then .Ok ()
      else .Err .BadSignature ⦄ := by
  have hpos := tagLen_pos a
  obtain ⟨e, he⟩ := hr.1
  unfold mid.pbkdf2_vg.Key.verify
  rw [he, bind_ok]
  have hlv : (Slice.len prev).val = prev.length := Slice.len_val prev
  by_cases hs : prev.length < tagLen a
  · have : Slice.len prev < key.tag_len := by
      rw [UScalar.lt_equiv, hlv, hk.2.1]; exact hs
    simp only [this, ↓reduceIte, hs, true_or, WP.spec_ok]
  have hs' : ¬ Slice.len prev < key.tag_len := by
    rw [UScalar.lt_equiv, hlv, hk.2.1]; exact hs
  simp only [hs', ↓reduceIte, hs, false_or]
  apply WP.spec_bind (vg_check_len_spec a P key hk (Slice.len prev))
  rintro c rfl
  rw [hlv]
  by_cases hc : (prev.length + tagLen a - 1) / tagLen a ≤ U32.max
  · have hc' : 0 < prev.length ∧ (prev.length + tagLen a - 1) / tagLen a ≤ U32.max :=
      ⟨by omega, hc⟩
    simp only [hc', and_self, not_true_eq_false, ↓reduceIte,
      core.result.Result.Insts.CoreOpsTry.branch, bind_ok, low.generic.zeroise.ZeroableRef.get]
    apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneU8 0#u8 (Slice.len prev) rfl)
    rintro v ⟨-, hvl⟩
    apply WP.spec_bind (key_bytes_spec a P key hk)
    intro s hks
    rw [hk.1]
    simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
    have hol : v.slice.length = prev.length := by
      rw [← hlv, ← hvl]; rfl
    apply WP.spec_bind (vg_derive_spec a s salt iterations v.slice hi
      (by rw [hol]; exact (ceilDiv_le_iff _ _ hpos).mp hc))
    rintro r ⟨hrl, hrb⟩
    apply WP.spec_bind (ct_equal_spec hr.held _ prev)
    rintro eq rfl
    obtain ⟨s', hs'⟩ := hz r
    simp only [bind_ok, low.ct.into_public]
    have hzs : low.generic.zeroise.zeroise U8.Insts.RindLowGenericZeroiseZeroable r ⦃ _ => True ⦄ := by
      rw [hs']; simp
    step with hzs as ⟨z⟩
    have hd : (alloc.vec.Vec.deref ({ slice := r } : alloc.vec.Vec U8)).val = r.val := by
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
    rw [hd]
    have hp : bv r.val =
        pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val prev.length := by
      rw [hrb, hks, hol]
      exact pbkdf2_congr _ _ _ _ (hmacOf_vgKeyBytes a hr P) _ _ _
    have hiff : r.val = prev.val ↔ bv prev.val =
        pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val prev.length := by
      rw [← hp, bv_inj, eq_comm]
    by_cases hb : r.val = prev.val
    · simp only [hb, decide_true, ↓reduceIte, hiff.mp hb, WP.spec_ok]
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, mt hiff.mpr hb, WP.spec_ok]
  · simp only [hc, not_false_eq_true, ↓reduceIte,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp

/-! ## `Key::new` -/

theorem sha1_context_new_spec : mid.sha1.Sha1Context.new ⦃ c => Sha1Ctx [] c ⦄ := by
  unfold mid.sha1.Sha1Context.new
  step with sha1_new_spec as ⟨s, hs⟩
  exact sha1_resume_spec [] s hs

theorem sha256_context_new_spec : mid.sha2.Sha256Context.new ⦃ c => Sha256Ctx [] c ⦄ := by
  unfold mid.sha2.Sha256Context.new
  step with sha256_new_spec as ⟨s, hs⟩
  exact sha256_resume_spec [] s hs

theorem sha384_context_new_spec :
    mid.sha2.Sha384Context.new ⦃ c => Hashed sha384Iv c.inner [] ⦄ := by
  simp only [mid.sha2.Sha384Context.new, mid.sha2.Sha384Context.resume]
  step with sha384_initial_spec as ⟨st, hh, hn⟩
  step with resume_spec _ st hh hn as ⟨c, hc⟩
  simpa using hc

theorem sha512_context_new_spec : mid.sha2.Sha512Context.new ⦃ c => Hashed sha512Iv c [] ⦄ := by
  simp only [mid.sha2.Sha512Context.new]
  step with sha512_initial_spec as ⟨st, hh, hn⟩
  step with resume_spec _ st hh hn as ⟨c, hc⟩
  simpa using hc

theorem sha384_context_update_spec (h : RunsSha512) (c : mid.sha2.Sha384Context) (m : List U8)
    (b : Slice U8) (hc : Hashed sha384Iv c.inner m) (hl : m.length + b.length ≤ maxInput) :
    mid.sha2.Sha384Context.update c b ⦃ c' => Hashed sha384Iv c'.inner (m ++ b.val) ⦄ := by
  simp only [mid.sha2.Sha384Context.update]
  step with context_update_spec h _ c.inner m b hc (maxInput_lt _ hl) as ⟨c', h'⟩
  exact h'

theorem sha384_context_finish_spec (h : RunsSha512) (c : mid.sha2.Sha384Context) (m : List U8)
    (hc : Hashed sha384Iv c.inner m) :
    mid.sha2.Sha384Context.finish c ⦃ r => r.val = sha384 m ⦄ := by
  simp only [mid.sha2.Sha384Context.finish]
  step with context_finish_spec h _ c.inner m hc as ⟨r, hr⟩
  apply WP.spec_mono (sha384_truncate_spec r)
  intro t ht
  rw [ht, hr, sha384]

theorem sha512_context_finish_spec (h : RunsSha512) (c : mid.sha2.Sha512Context) (m : List U8)
    (hc : Hashed sha512Iv c m) :
    mid.sha2.Sha512Context.finish c ⦃ r => r.val = sha512 m ⦄ := by
  apply WP.spec_mono (context_finish_spec h _ c m hc)
  intro r hr
  rw [hr, sha512]

/-- Copying `src` into the front of `key`, as `hmac_key` does. -/
theorem copy_front_spec (key : Std.Array U8 128#usize) (src : Slice U8) (hs : src.length ≤ 128) :
    (do
      let (s, back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U8)) key { «end» := Slice.len src }
      let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
      ok (Slice.len src, back s1)) ⦃ p => p.1.val ≤ 128 ∧ p.2.val.take p.1.val = src.val ⦄ := by
  have hkl : key.val.length = 128 := key.property
  have hlv : (Slice.len src).val = src.length := Slice.len_val src
  step with Array.index_mut_SliceIndexRangeToUsizeSlice key { «end» := Slice.len src }
    (by scalar_tac) as ⟨s, back, hs1, hs2, hs3⟩
  step with core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU8 s src
    (by rw [hs2, hlv]) as ⟨s1, hs1e⟩
  refine ⟨by omega, ?_⟩
  rw [hs3, hlv, hs1e]
  have := take_setSlice! key.val src.val 0 (by simp only [Slice.length] at hs; omega)
  simpa [Slice.length] using this

/-- `hmac_key` keeps `secret`, or its hash if it is longer than a block, in
the front of `key`. -/
theorem vg_hmac_key_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (secret : Slice U8)
    (hl : secret.length ≤ maxInput) (key : Std.Array U8 128#usize) :
    mid.pbkdf2_vg.Algorithm.hmac_key (vgAlg a) secret key ⦃ p =>
      p.1.val ≤ 128 ∧ bv (p.2.val.take p.1.val) = vgKeyBytes a (bv secret.val) ⦄ := by
  obtain ⟨-, hc⟩ := hr
  have hkl : key.val.length = 128 := key.property
  unfold mid.pbkdf2_vg.Algorithm.hmac_key
  cases a <;> simp only [vgAlg, vgKeyBytes, hmacBlock, hmacHash, bv_length,
    mid.sha1.Sha1Context.BLOCK_SZ, mid.sha2.Sha256Context.BLOCK_SZ, mid.sha2.Sha512Context.BLOCK_SZ,
    bind_ok] at hc ⊢
  all_goals split
  all_goals rename_i hb
  · replace hb : secret.val.length ≤ 64 := by scalar_tac
    apply WP.spec_mono (copy_front_spec key secret (by simp only [Slice.length]; omega))
    rintro p ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, ite_eq_left hb]⟩
  · replace hb : ¬ secret.val.length ≤ 64 := by scalar_tac
    step with sha1_context_new_spec as ⟨c, hc0⟩
    step with sha1_ctx_update_spec hc [] c secret hc0 (by simpa using hl) as ⟨c1, hc1⟩
    step with sha1_ctx_finish_spec hc _ c1 hc1 (by simpa using hl) as ⟨d, hd⟩
    simp only [lift, bind_ok]
    apply WP.spec_mono (copy_front_spec key d.to_slice (by simp))
    rintro p ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, Array.val_to_slice, hd, ite_eq_right hb, List.nil_append]
  · replace hb : secret.val.length ≤ 64 := by scalar_tac
    apply WP.spec_mono (copy_front_spec key secret (by simp only [Slice.length]; omega))
    rintro p ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, ite_eq_left hb]⟩
  · replace hb : ¬ secret.val.length ≤ 64 := by scalar_tac
    step with sha256_context_new_spec as ⟨c, hc0⟩
    step with sha256_ctx_update_spec hc [] c secret hc0 (by simpa using hl) as ⟨c1, hc1⟩
    step with sha256_ctx_finish_spec hc _ c1 hc1 (by simpa using hl) as ⟨d, hd⟩
    simp only [lift, bind_ok]
    apply WP.spec_mono (copy_front_spec key d.to_slice (by simp))
    rintro p ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, Array.val_to_slice, hd, ite_eq_right hb, List.nil_append]
  · replace hb : secret.val.length ≤ 128 := by scalar_tac
    apply WP.spec_mono (copy_front_spec key secret (by simp only [Slice.length]; omega))
    rintro p ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, ite_eq_left hb]⟩
  · replace hb : ¬ secret.val.length ≤ 128 := by scalar_tac
    step with sha384_context_new_spec as ⟨c, hc0⟩
    step with sha384_context_update_spec hc c [] secret hc0 (by simpa using hl) as ⟨c1, hc1⟩
    step with sha384_context_finish_spec hc c1 _ hc1 as ⟨d, hd⟩
    simp only [lift, bind_ok]
    apply WP.spec_mono (copy_front_spec key d.to_slice (by simp))
    rintro p ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, Array.val_to_slice, hd, ite_eq_right hb, List.nil_append, sha384Bytes, ofBv_bv]
  · replace hb : secret.val.length ≤ 128 := by scalar_tac
    apply WP.spec_mono (copy_front_spec key secret (by simp only [Slice.length]; omega))
    rintro p ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, ite_eq_left hb]⟩
  · replace hb : ¬ secret.val.length ≤ 128 := by scalar_tac
    step with sha512_context_new_spec as ⟨c, hc0⟩
    step with context_update_spec hc _ c [] secret hc0 (maxInput_lt _ (by simpa using hl))
      as ⟨c1, hc1⟩
    step with sha512_context_finish_spec hc c1 _ hc1 as ⟨d, hd⟩
    simp only [lift, bind_ok]
    apply WP.spec_mono (copy_front_spec key d.to_slice (by simp))
    rintro p ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, Array.val_to_slice, hd, ite_eq_right hb, List.nil_append, sha512Bytes, ofBv_bv]

/-- `Algorithm::routine` names `a`'s routine, when the CPU runs it. -/
theorem vg_routine_spec (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (hcpu : ∃ o, low.aarch64.cpu.HaveCryptoExt.check = ok o) :
    mid.pbkdf2_vg.Algorithm.routine (vgAlg a) ⦃ o => ∀ p, o = some p → p = vgHash a ⦄ := by
  obtain ⟨-, hc⟩ := hr
  cases a <;> simp only [vgAlg, vgHash, mid.pbkdf2_vg.Algorithm.routine] at hc ⊢
  · unfold low.aarch64.pbkdf2_vg.Pbkdf2.sha1
    obtain ⟨o, ho⟩ := hcpu
    rw [ho, bind_ok]
    cases o <;> simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  · unfold low.aarch64.pbkdf2_vg.Pbkdf2.sha256
    obtain ⟨o, ho⟩ := hc.crypto
    rw [ho, bind_ok]
    simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  · unfold low.aarch64.pbkdf2_vg.Pbkdf2.sha384
    obtain ⟨o, ho⟩ := hc.2.2
    rw [ho, bind_ok]
    cases o <;> simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  · unfold low.aarch64.pbkdf2_vg.Pbkdf2.sha512
    obtain ⟨o, ho⟩ := hc.2.2
    rw [ho, bind_ok]
    cases o <;> simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

/-- `Key::new` keys VG's routine with `secret`'s HMAC key, when the CPU runs
it. -/
theorem vg_key_new_spec (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (hcpu : ∃ o, low.aarch64.cpu.HaveCryptoExt.check = ok o) (secret : Slice U8)
    (hl : secret.length ≤ maxInput) :
    mid.pbkdf2_vg.Key.new (vgAlg a) secret ⦃ o =>
      ∀ key, o = some key → VgKeyOf a (bv secret.val) key ⦄ := by
  obtain ⟨e, he⟩ := hr.1
  unfold mid.pbkdf2_vg.Key.new
  apply WP.spec_bind (vg_routine_spec a hr hcpu)
  rintro (_ | p) hp
  · simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  · simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok, he,
      low.generic.zeroise.ZeroableRef.new]
    apply WP.spec_bind (vg_hmac_key_spec a hr secret hl _)
    rintro ⟨len, k⟩ ⟨h1, h2⟩
    have ht : ∃ n, mid.pbkdf2_vg.Algorithm.tag_len (vgAlg a) = ok n ∧ n.val = tagLen a := by
      cases a <;> exact ⟨_, rfl, by
        simp [mid.sha1.Sha1Context.OUTPUT_SZ, mid.sha2.Sha256Context.OUTPUT_SZ,
          mid.sha2.Sha384Context.OUTPUT_SZ, mid.sha2.Sha512Context.OUTPUT_SZ, tagLen]⟩
    obtain ⟨n, hn, hnv⟩ := ht
    simp only [bind_ok, hn]
    show (ok (some { routine := p, tag_len := n, key := k, len := len } : Option mid.pbkdf2_vg.Key))
      ⦃ _ ⦄
    simp only [WP.spec_ok]
    rintro key ⟨⟩
    exact ⟨hp p rfl, hnv, h1, h2⟩

/-! ## `Secret` -/

/-- `s` is a `Secret` of the password `P` under `a`, on either branch. -/
def SecretOf (a : high.hmac.Algorithm) (P : List Byte) : high.pbkdf2.Secret → Prop
  | .Rind k => KeyOf a P k
  | .Vg alg key => alg = a ∧ VgKeyOf a P key

/-- `Secret::new` keys `secret` under `algorithm`'s HMAC, on whichever of
VG's routine and rind's loop it picks, given that the CPU check returns; it
does not prove which it picks. -/
theorem secret_new_spec (algorithm : high.pbkdf2.Algorithm) (a : high.hmac.Algorithm)
    (ha : algorithm.hmac = a) (hv : algorithm.vg = vgAlg a) (hr : RunsHmac a)
    (hcpu : ∃ o, low.aarch64.cpu.HaveCryptoExt.check = ok o) (secret : Slice U8)
    (hl : secret.length ≤ maxInput) :
    high.pbkdf2.Secret.new algorithm secret ⦃ s => SecretOf a (bv secret.val) s ⦄ := by
  unfold high.pbkdf2.Secret.new
  rw [hv]
  apply WP.spec_bind (vg_key_new_spec a hr hcpu secret hl)
  rintro (_ | key) hk
  · rw [ha]
    apply WP.spec_bind (rind.aarch64.key_new_spec a hr secret hl)
    intro k hk'
    simp only [WP.spec_ok]
    exact hk'
  · simp only [low.generic.zeroise.ZeroableRef.new, bind_ok, WP.spec_ok]
    exact ⟨ha, hk key rfl⟩

/-- `Secret::derive` writes PBKDF2's output, for an output of at least one
and at most `u32::MAX` blocks, and refuses any other, on either branch. -/
theorem secret_derive_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (s : high.pbkdf2.Secret) (hs : SecretOf a P s)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (hi : 0 < iterations.val) (salt out : Slice U8)
    (hm : hmacBlock a + salt.length + 4 ≤ maxInput) :
    high.pbkdf2.Secret.derive s iterations salt out ⦃ r =>
      if 0 < out.length ∧ (out.length + tagLen a - 1) / tagLen a ≤ U32.max then
        r.1 = .Ok () ∧ r.2.length = out.length ∧
          bv r.2.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val out.length
      else r = (.Err .WrongLength, out) ⦄ := by
  cases s with
  | Rind k => exact derive_spec a hr P k hs iterations salt out hm
  | Vg alg key =>
    unfold high.pbkdf2.Secret.derive
    exact vg_key_derive_spec a hr P key hs.2 iterations hi salt out

/-- `Secret::verify` accepts exactly PBKDF2's output, of at least the tag's
length and at most `u32::MAX` blocks, on either branch. -/
theorem secret_verify_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (hz : ZeroiseReturns)
    (P : List Byte) (s : high.pbkdf2.Secret) (hs : SecretOf a P s)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (hi : 0 < iterations.val) (salt prev : Slice U8)
    (hm : hmacBlock a + salt.length + 4 ≤ maxInput) :
    high.pbkdf2.Secret.verify s iterations salt prev ⦃ r =>
      r = if prev.length < tagLen a ∨ ¬ (prev.length + tagLen a - 1) / tagLen a ≤ U32.max then
        .Err .WrongLength
      else if bv prev.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val
          prev.length then .Ok ()
      else .Err .BadSignature ⦄ := by
  cases s with
  | Rind k => exact verify_spec a hr P k hs iterations salt prev hm
  | Vg alg key =>
    unfold high.pbkdf2.Secret.verify
    exact vg_key_verify_spec a hr hz P key hs.2 iterations hi salt prev

end rind.aarch64.kdf
