import Rind.X86_64.Hkdf
open Aeneas Aeneas.Std Result rind.spec

/-!
# PBKDF2's API, `high::pbkdf2`

`Secret::derive` writes RFC 8018's PBKDF2 and `Secret::verify` accepts exactly
it, over HMAC with any of `high::hmac`'s hashes, down to
`Rind.X86_64.HmacApi`, for a `Secret` on rind's loop, `Rind`. On aarch64 a
`Secret` runs pyca/verified-garbage's routine instead where the CPU has the
instructions it takes, which `mid::pbkdf2_vg` wraps: `Rind.Aarch64.Pbkdf2Vg`
proves that branch. `Secret` is translated in the second Aeneas pass.
`admin/prove` writes the aarch64 proof from this file by renaming the target.
-/

namespace rind.x86_64.kdf

/-! ## PBKDF2's blocks -/

section
variable (prf : List Byte → List Byte → List Byte) (P S : List Byte)

/-- One PBKDF2 iteration: `U_j` from `U_(j-1)`, XORed into the sum. -/
def pbStep (acc : List Byte × List Byte) : List Byte × List Byte :=
  let u := prf P acc.1
  (u, List.zipWith (· ^^^ ·) acc.2 u)

/-- `U_1` of block `i`. -/
def pbU1 (i : Nat) : List Byte := prf P (S ++ (BitVec.ofNat 32 i).toBEBytes)

/-- `k` iterations from `acc`. -/
def pbIter (k : Nat) (acc : List Byte × List Byte) : List Byte × List Byte :=
  (List.range k).foldl (fun acc _ => pbStep prf P acc) acc

/-- Block `T_i` after `c` iterations. -/
def pbT (c i : Nat) : List Byte := (pbIter prf P (c - 1) (pbU1 prf P S i, pbU1 prf P S i)).2

theorem pbkdf2_eq (n c L : Nat) :
    pbkdf2 prf n P S c L = (blocksOut (pbT prf P S c) ((L + n - 1) / n)).take L := rfl

theorem pbIter_succ (k : Nat) (acc : List Byte × List Byte) :
    pbIter prf P (k + 1) acc = pbStep prf P (pbIter prf P k acc) := by
  simp [pbIter, List.range_succ, List.foldl_append]

theorem pbIter_length (n : Nat) (hn : ∀ x, (prf P x).length = n) (k : Nat)
    (acc : List Byte × List Byte) (h1 : acc.1.length = n) (h2 : acc.2.length = n) :
    (pbIter prf P k acc).1.length = n ∧ (pbIter prf P k acc).2.length = n := by
  induction k with
  | zero => exact ⟨h1, h2⟩
  | succ k ih =>
    rw [pbIter_succ]
    simp only [pbStep, List.length_zipWith, hn, ih.2, min_self, and_self]

theorem pbT_length (n : Nat) (hn : ∀ x, (prf P x).length = n) (c i : Nat) :
    (pbT prf P S c i).length = n :=
  (pbIter_length prf P n hn _ _ (hn _) (hn _)).2

end

/-! ## `Rind::block` -/

/-- `S` with its bytes before `k` XORed with `N`'s. -/
def xorUpTo (S N : List U8) (k : Nat) : List U8 :=
  S.mapIdx fun j x => if j < k then x ^^^ N[j]! else x

theorem xorUpTo_step (S N : List U8) (i : Nat) (hi : i < S.length) :
    (xorUpTo S N i).set i (S[i] ^^^ N[i]!) = xorUpTo S N (i + 1) := by
  simp only [xorUpTo]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_set]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h, List.getElem_mapIdx, List.getElem_mapIdx]
    by_cases hj : j < i
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right (by omega)]

theorem xorUpTo_zero (S N : List U8) : xorUpTo S N 0 = S := by
  apply List.ext_getElem (by simp [xorUpTo])
  intro j h1 h2
  simp [xorUpTo]

theorem xorUpTo_end (S N : List U8) (hN : N.length = S.length) :
    bv (xorUpTo S N S.length) = List.zipWith (· ^^^ ·) (bv S) (bv N) := by
  apply List.ext_getElem (by simp [bv, xorUpTo, hN])
  intro j h1 h2
  simp only [bv, xorUpTo, List.length_map, List.length_mapIdx] at h1
  simp only [bv, xorUpTo, List.getElem_map, List.getElem_mapIdx, List.getElem_zipWith,
    ite_eq_left h1, UScalar.bv_xor]
  rw [getElem!_pos N j (by omega)]

theorem xor_loop_spec (S N : Slice U8) (hN : N.length = S.length) :
    ∀ (j : Usize) (sum : Slice U8), j.val ≤ S.length → sum.val = xorUpTo S.val N.val j.val →
    high.pbkdf2.Rind.block_loop0_loop0 { start := j, «end» := S.len } sum N ⦃ r =>
      bv r.val = List.zipWith (· ^^^ ·) (bv S.val) (bv N.val) ⦄ := by
  intro j sum hj hs
  unfold high.pbkdf2.Rind.block_loop0_loop0
  apply loop.spec_decr_nat (fun x => S.length - x.1.start.val)
    (fun x => x.1.«end» = S.len ∧ x.1.start.val ≤ S.length ∧
      x.2.val = xorUpTo S.val N.val x.1.start.val)
  · rintro ⟨it, sm⟩ ⟨he, hle, hsm⟩
    simp only at he hle hsm ⊢
    unfold high.pbkdf2.Rind.block_loop0_loop0.body
    have hS : it.«end».val = S.length := by rw [he, Slice.len_val]
    step as ⟨o, iter1, ho, hend⟩
    by_cases hlt : it.start.val < it.«end».val
    · simp only [hlt, ↓reduceIte] at ho
      obtain ⟨rfl, hst⟩ := ho
      simp only
      have hNl : N.val.length = S.val.length := hN
      have hSl : S.val.length = S.length := rfl
      have hsml : sm.val.length = S.length := by rw [hsm]; simp [xorUpTo]
      have hk : it.start.val < S.val.length := by rw [hSl, ← hS]; exact hlt
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step*
      have h2 : i2 = S.val[it.start.val] := by
        rw [hi2]; simp [hsm, xorUpTo]
      have h3 : i3 = S.val[it.start.val] ^^^ N.val[it.start.val]! := by
        apply UScalar.eq_of_val_eq
        rw [i3_post, h2, hi1, getElem!_pos N.val _ (by omega)]
      refine ⟨by rw [hend, he], by omega, ?_, by omega⟩
      rw [s_post, Slice.set_val_eq, hsm, h3, xorUpTo_step _ _ _ hk, hst]
    · simp only [hlt, ↓reduceIte] at ho
      obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val = S.val.length := by simp only [Slice.length] at hle hS; omega
      rw [hsm, this]
      exact xorUpTo_end _ _ hN
  · exact ⟨rfl, hj, hs⟩

theorem digest_as_mut_spec (d : high.digest.Digest) :
    high.digest.Digest.as_mut d ⦃ s back =>
      s.length = outLen d.algorithm ∧ bv s.val = digestBytes d ∧
        ∀ s' : Slice U8, s'.length = outLen d.algorithm →
          (back s').algorithm = d.algorithm ∧ digestBytes (back s') = bv s'.val ⦄ := by
  obtain ⟨n, hn, hnv, hn64⟩ := output_len_eq d.algorithm
  unfold high.digest.Digest.as_mut
  simp only [hn, bind_ok]
  step*
  have hvl : (d.value.val).length = 64 := d.value.property
  refine ⟨by rw [s_post1, hnv], ?_, ?_⟩
  · rw [digestBytes, s_post, ← hnv]
    simp [List.slice]
  · intro s' hs'
    simp only [digestBytes, s_post2]
    have := take_setSlice! d.value.val s'.val 0 (by simp only [Slice.length] at hs'; omega)
    simp only [List.take_zero, List.nil_append, Nat.zero_add] at this
    simp only [Slice.length] at hs'
    rw [← hs', this]

/-- The iterations after `U_1`: `u` is the last `U_j` and `t` their sum. -/
theorem block_loop_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a P k) (c : Nat) (acc : List Byte × List Byte) :
    ∀ (iter : core.ops.range.Range U32) (u t : high.digest.Digest),
      iter.«end».val = c → 1 ≤ iter.start.val → iter.start.val - 1 ≤ c - 1 →
      outLen u.algorithm = tagLen a → outLen t.algorithm = tagLen a →
      digestBytes u = (pbIter (hmacOf a) P (iter.start.val - 1) acc).1 →
      digestBytes t = (pbIter (hmacOf a) P (iter.start.val - 1) acc).2 →
      high.pbkdf2.Rind.block_loop0 iter k u t ⦃ r =>
        outLen r.algorithm = tagLen a ∧ digestBytes r = (pbIter (hmacOf a) P (c - 1) acc).2 ⦄ := by
  intro iter u t he h1 hle hul htl hu ht
  unfold high.pbkdf2.Rind.block_loop0
  apply loop.spec_decr_nat (fun x => c - x.1.start.val)
    (fun x => x.2.1 = k ∧ x.1.«end».val = c ∧ 1 ≤ x.1.start.val ∧ x.1.start.val - 1 ≤ c - 1 ∧
      outLen x.2.2.1.algorithm = tagLen a ∧ outLen x.2.2.2.algorithm = tagLen a ∧
      digestBytes x.2.2.1 = (pbIter (hmacOf a) P (x.1.start.val - 1) acc).1 ∧
      digestBytes x.2.2.2 = (pbIter (hmacOf a) P (x.1.start.val - 1) acc).2)
  · rintro ⟨it, sf, u, t⟩ ⟨rfl, he, h1, hle, hul, htl, hu, ht⟩
    simp only at he h1 hle hul htl hu ht ⊢
    unfold high.pbkdf2.Rind.block_loop0.body
    step as ⟨o, iter1, ho, hend⟩
    by_cases hlt : it.start.val < it.«end».val
    · simp only [hlt, ↓reduceIte] at ho
      obtain ⟨rfl, hst⟩ := ho
      simp only
      step with digest_as_ref_spec u as ⟨s, hsl, hsb⟩
      apply WP.spec_bind (key_tag_spec a hr P sf hk s (by
        have h64 : hmacBlock a + tagLen a ≤ 192 := by cases a <;> decide
        rw [hsl, hul]; unfold maxInput; simp only [U64.max_eq]; omega))
      rintro u1 ⟨hu1l, hu1b⟩
      step with digest_as_mut_spec t as ⟨sum, back, hsuml, hsumb, hback⟩
      step with digest_as_ref_spec u1 as ⟨s1, hs1l, hs1b⟩
      step as ⟨next, hnext, hnextl⟩
      have hnv : next.val = s1.val := by
        rw [hnext, List.slice, List.drop_zero, Nat.sub_zero, Slice.len_val]
        exact List.take_of_length_le (by simp only [Slice.length] at hsuml hs1l ⊢; omega)
      apply WP.spec_bind (xor_loop_spec sum next (by rw [hnextl, Slice.len_val]) 0#usize sum
        (by show (0 : Nat) ≤ _; exact Nat.zero_le _)
        (by show sum.val = xorUpTo sum.val next.val 0; rw [xorUpTo_zero]))
      intro sum1 hsum1
      have hsum1l : sum1.length = outLen t.algorithm := by
        have := congrArg List.length hsum1
        simp only [bv_length, List.length_zipWith] at this
        simp only [Slice.length, hnv] at this hsuml hs1l ⊢
        omega
      obtain ⟨hba, hbb⟩ := hback sum1 hsum1l
      simp only [WP.spec_ok]
      refine ⟨by trivial, by rw [hend]; exact he, by omega, by omega, hu1l, by rw [hba]; exact htl, ?_, ?_,
        by omega⟩
      · rw [hu1b, hsb, hu, hst, Nat.add_sub_cancel, show it.start.val = it.start.val - 1 + 1 by omega,
          pbIter_succ]
        rfl
      · rw [hbb, hsum1, hsumb, hnv, hs1b, hu1b, hsb, hu, ht, hst, Nat.add_sub_cancel,
          show it.start.val = it.start.val - 1 + 1 by omega, pbIter_succ]
        rfl
    · simp only [hlt, ↓reduceIte] at ho
      obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : it.start.val - 1 = c - 1 := by omega
      rw [← this]
      exact ⟨htl, ht⟩
  · exact ⟨rfl, he, h1, hle, hul, htl, hu, ht⟩

theorem bv_toBEBytes (x : U32) :
    bv (x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)) = (BitVec.ofNat 32 x.val).toBEBytes := by
  simp only [bv, List.map_map]
  rw [show ((fun x : U8 => x.bv) ∘ @UScalar.mk UScalarTy.U8) = id from rfl, List.map_id]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt x.bv.isLt).symm

/-- `Rind::block` is PBKDF2's block `T_index` after `iterations` iterations. -/
theorem block_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a P k) (salt : List U8) (salted : high.hmac.Streaming)
    (hs : StreamOf a P salt salted) (hm : hmacBlock a + salt.length + 4 ≤ maxInput)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (index : U32) :
    high.pbkdf2.Rind.block k salted iterations index ⦃ r =>
      outLen r.algorithm = tagLen a ∧
        digestBytes r = pbT (hmacOf a) P (bv salt) iterations.val index.val ⦄ := by
  unfold high.pbkdf2.Rind.block
  apply WP.spec_bind (stream_clone_spec a hr P salt salted hs)
  intro ctx hctx
  step as ⟨arr, harr⟩
  step as ⟨sl, hsl⟩
  apply WP.spec_bind (stream_update_spec a hr P salt ctx hctx sl (by
    have : sl.length = 4 := by simp [Slice.length, hsl]
    rw [this]; exact hm))
  intro ctx1 hctx1
  apply WP.spec_bind (stream_finish_spec a hr P _ ctx1 hctx1 (by
    have : sl.val.length = 4 := by simp [hsl]
    simp only [List.length_append, this]; omega))
  rintro u ⟨hul, hub⟩
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  have hU1 : digestBytes u = pbU1 (hmacOf a) P (bv salt) index.val := by
    rw [hub, pbU1, bv_append, hsl, Array.val_to_slice, harr, bv_toBEBytes]
  apply WP.spec_mono (block_loop_spec a hr P k hk iterations.val
    (pbU1 (hmacOf a) P (bv salt) index.val, pbU1 (hmacOf a) P (bv salt) index.val) _ u u rfl
    (by simp) (by simp) hul hul (by simp [pbIter, hU1]) (by simp [pbIter, hU1]))
  rintro r ⟨hrl, hrb⟩
  exact ⟨hrl, hrb⟩

/-! ## The block iterator, `(1..=u32::MAX).zip((0..len).step_by(hash_len))` -/

/-- The iterator's type. -/
abbrev BlockIter := core.iter.adapters.zip.Zip (core.ops.range.RangeInclusive U32)
  (core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))

/-- The iterator before block `i'` + 1, of `n`-byte blocks over `L` bytes: the
indices from `i' + 1` and the offsets from `i' * n`. -/
def ZipAt (n L i' : Nat) (it : BlockIter) : Prop :=
  it.fst.«end».val = U32.max ∧ (it.fst.exhausted = false → it.fst.start.val = i' + 1) ∧
    (it.fst.exhausted = true → L ≤ i' * n) ∧
    it.snd.iter.start.val = min (i' * n) L ∧ it.snd.iter.«end».val = L ∧ it.snd.step_by.val = n

theorem zip_next_spec (n L i' : Nat) (hn : 0 < n) (hK : (L + n - 1) / n ≤ U32.max)
    (it : BlockIter) (hz : ZipAt n L i' it) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator core.iter.range.StepU32)
      (core.iter.traits.iterator.IteratorStepBy
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)) it ⦃ o it' =>
      match o with
      | none => L ≤ i' * n
      | some (idx, off) => idx.val = i' + 1 ∧ off.val = i' * n ∧ i' * n < L ∧
          ZipAt n L (i' + 1) it' ⦄ := by
  obtain ⟨hend, hne, hex, hs, hse, hsb⟩ := hz
  unfold core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
  step as ⟨oa, a', hoa⟩
  have hsmax : it.fst.start.val ≤ U32.max := by scalar_tac
  by_cases hx : it.fst.exhausted = true ∨ it.fst.«end».val < it.fst.start.val
  · simp only [hx, ↓reduceIte] at hoa
    obtain ⟨rfl, -⟩ := hoa
    simp only [WP.spec_ok]
    rcases hx with hx | hx
    · exact hex hx
    · omega
  · simp only [hx, ↓reduceIte] at hoa
    simp only [not_or, not_lt] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hnx : it.fst.exhausted = false := by simpa using hx1
    have hst : it.fst.start.val = i' + 1 := hne hnx
    have hoa' : oa = some it.fst.start := by split at hoa <;> exact hoa.1
    subst hoa'
    simp only
    step as ⟨ob, b', hob, hbe, hbs⟩
    by_cases hb : it.snd.iter.start.val < it.snd.iter.«end».val
    · simp only [hb, ↓reduceIte] at hob
      obtain ⟨rfl, hb'⟩ := hob
      simp only [WP.spec_ok]
      have hoff : i' * n < L := by rw [hs, hse] at hb; omega
      refine ⟨hst, by rw [hs]; omega, hoff, ?_⟩
      have hb'' : b'.iter.start.val = min ((i' + 1) * n) L := by
        rw [hb', hs, hsb, hse, Nat.add_mul, one_mul]; omega
      split at hoa
      · rename_i hlt
        obtain ⟨-, ha1, ha2, ha3⟩ := hoa
        exact ⟨by rw [ha2]; exact hend, fun _ => by rw [ha1, hst], fun h => by simp_all,
          hb'', by rw [hbe, hse], by rw [hbs, hsb]⟩
      · rename_i hlt
        obtain ⟨-, ha1, ha2, ha3⟩ := hoa
        have hi : i' + 1 = U32.max := by
          simp only [not_lt] at hlt
          omega
        have hL : L ≤ (i' + 1) * n := by
          have := ceilDiv_ge n L hn
          have : (L + n - 1) / n * n ≤ (i' + 1) * n := Nat.mul_le_mul_right _ (by omega)
          omega
        exact ⟨by rw [ha2]; exact hend, fun h => by simp_all, fun _ => hL,
          hb'', by rw [hbe, hse], by rw [hbs, hsb]⟩
    · simp only [hb, ↓reduceIte] at hob
      obtain ⟨rfl, -⟩ := hob
      simp only [WP.spec_ok]
      rw [hs, hse] at hb
      show L ≤ i' * n
      omega

theorem zipAt_measure (n L i' : Nat) (it it' : BlockIter) (hz : ZipAt n L i' it)
    (hz' : ZipAt n L (i' + 1) it') (hn : 0 < n) (hlt : i' * n < L) :
    L - it'.snd.iter.start.val < L - it.snd.iter.start.val := by
  rw [hz.2.2.2.1, hz'.2.2.2.1, Nat.add_mul, one_mul]
  omega

/-! ## `Rind::derive` -/

theorem salted_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a P k) (salt : Slice U8)
    (hm : hmacBlock a + salt.length ≤ maxInput) :
    high.pbkdf2.Rind.salted k salt ⦃ s => StreamOf a P salt.val s ⦄ := by
  unfold high.pbkdf2.Rind.salted
  apply WP.spec_bind (key_start_spec a hr P k hk)
  intro s hs
  have := stream_update_spec a hr P [] s hs salt (by simpa using hm)
  simpa using this

theorem derive_loop_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a P k) (salt : List U8) (salted : high.hmac.Streaming)
    (hs : StreamOf a P salt salted) (hm : hmacBlock a + salt.length + 4 ≤ maxInput)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (hash_len : Usize) (hhl : hash_len.val = tagLen a) (L : Nat)
    (hK : (L + tagLen a - 1) / tagLen a ≤ U32.max) (it : BlockIter) (out : Slice U8) (i' : Nat)
    (hz : ZipAt (tagLen a) L i' it) (hl : out.length = L)
    (hpre : (bv out.val).take (i' * tagLen a) =
      (blocksOut (pbT (hmacOf a) P (bv salt) iterations.val) i').take L) :
    high.pbkdf2.Rind.derive_loop it k iterations out salted hash_len ⦃ r =>
      r.length = L ∧ bv r.val = (blocksOut (pbT (hmacOf a) P (bv salt) iterations.val)
        ((L + tagLen a - 1) / tagLen a)).take L ⦄ := by
  have hn := tagLen_pos a
  have hT : ∀ i, (pbT (hmacOf a) P (bv salt) iterations.val (i + 1)).length = tagLen a :=
    fun i => pbT_length _ _ _ _ (fun x => hmacOf_length a P x hr) _ _
  unfold high.pbkdf2.Rind.derive_loop
  apply loop.spec_decr_nat (fun x => L - x.1.snd.iter.start.val)
    (fun x => ∃ i', ZipAt (tagLen a) L i' x.1 ∧ x.2.length = L ∧
      (bv x.2.val).take (i' * tagLen a) =
        (blocksOut (pbT (hmacOf a) P (bv salt) iterations.val) i').take L)
  · rintro ⟨it, out⟩ ⟨i', hz, hl, hpre⟩
    simp only at hz hl hpre ⊢
    unfold high.pbkdf2.Rind.derive_loop.body
    apply WP.spec_bind (zip_next_spec _ L i' hn hK it hz)
    rintro ⟨o, it'⟩ ho
    rcases o with _ | ⟨idx, off⟩
    · simp only [WP.uncurry'] at ho
      refine (WP.spec_ok _).mpr ?_
      show out.length = L ∧ _
      have hbl : (bv out.val).length = L := by rw [bv_length]; exact hl
      refine ⟨hl, ?_⟩
      have := prefix_done _ _ hT hn (bv out.val) i' (by rw [hbl]; exact ho) (by rw [hbl]; exact hpre)
      rw [hbl] at this
      exact this
    · simp only [WP.uncurry'] at ho
      obtain ⟨hidx, hoff, hlt, hz'⟩ := ho
      dsimp only
      apply WP.spec_bind (block_spec a hr P k hk salt salted hs hm iterations idx)
      rintro blk ⟨hbl, hbb⟩
      have hol : (Slice.len out).val = L := by rw [Slice.len_val]; exact hl
      step as ⟨i1, hi1⟩
      step as ⟨len, hlen⟩
      step as ⟨i2, hi2⟩
      step as ⟨s, back, hsv, hsl, hback⟩
      step with digest_as_ref_spec blk as ⟨s1, hs1l, hs1b⟩
      step as ⟨s2, hs2v, hs2l⟩
      step as ⟨s3, hs3⟩
      · rw [hsl, hs2l, hi2]; omega
      have hlv : out.val.length = L := hl
      have hlenv : len.val = min (tagLen a) (L - i' * tagLen a) := by
        rw [hlen, core.cmp.impls.OrdUsize.min_val, hhl, hi1, hol, hoff]
      have hs2 : s2.val = s1.val.take (min (tagLen a) (L - i' * tagLen a)) := by
        rw [hs2v, List.slice, List.drop_zero, Nat.sub_zero, hlenv]
      have hs1l' : s1.val.length = tagLen a := by
        have : s1.length = tagLen a := by rw [hs1l, hbl]
        simpa only [Slice.length] using this
      have hT1 : bv s1.val = pbT (hmacOf a) P (bv salt) iterations.val (i' + 1) := by
        rw [hs1b, hbb, hidx]
      refine ⟨⟨i' + 1, hz', ?_, ?_⟩, zipAt_measure _ _ _ _ _ hz hz' hn hlt⟩
      · rw [hback, Slice.setSlice!_length]; exact hl
      · rw [hback, Slice.setSlice!_val, hs3, hs2, hoff]
        have := prefix_step _ _ hT out.val s1.val i' (by omega) hs1l' hT1 (by rw [hlv]; exact hpre)
        rw [hlv] at this
        exact this
  · exact ⟨i', hz, hl, hpre⟩

/-- `check_len` accepts a length of at least one and at most `u32::MAX` blocks. -/
theorem check_len_spec (a : high.hmac.Algorithm) (P : List Byte) (k : high.hmac.Key)
    (hk : KeyOf a P k) (len : Usize) :
    high.pbkdf2.Rind.check_len k len ⦃ r =>
      r = if 0 < len.val ∧ (len.val + tagLen a - 1) / tagLen a ≤ U32.max then .Ok ()
        else .Err .WrongLength ⦄ := by
  obtain ⟨n, hn, hnv⟩ := tagLen_eq a
  have hpos := tagLen_pos a
  unfold high.pbkdf2.Rind.check_len core.num.Usize.div_ceil
  rw [key_algorithm_eq hk, bind_ok, hn, bind_ok]
  have h0 : ¬ n.val = 0 := by omega
  simp only [h0, ↓reduceDIte, bind_ok]
  have hval : ∀ h, (UScalar.ofNatCore (ty := .Usize) ((len.val + n.val - 1) / n.val) h).val =
      (len.val + tagLen a - 1) / tagLen a := by
    intro h; rw [UScalar.ofNatCore_val_eq, hnv]
  have hcast : (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = U32.max := by
    simp only [UScalar.cast_val_eq, core.num.U32.MAX]
    rcases System.Platform.numBits_eq with h | h <;> simp [h, U32.rMax, U32.max, U32.numBits]
  split
  · rename_i hb
    have hB := congrArg UScalar.val hb
    rw [hval] at hB
    have hB' : (len.val + tagLen a - 1) / tagLen a = 0 := hB
    have hl0 : len.val = 0 := by
      by_contra hne
      have := (Nat.le_div_iff_mul_le hpos).mpr (show 1 * tagLen a ≤ len.val + tagLen a - 1 by omega)
      omega
    simp only [WP.spec_ok, hl0]
    simp
  · rename_i hb
    have hB : (len.val + tagLen a - 1) / tagLen a ≠ 0 := by
      intro h; apply hb; apply UScalar.eq_of_val_eq; rw [hval, h]; simp
    have hl0 : 0 < len.val := by
      by_contra h
      apply hB
      rw [show len.val = 0 by omega, Nat.zero_add]
      exact Nat.div_eq_of_lt (by omega)
    simp only [lift, bind_ok]
    split
    · rename_i hgt
      simp only [GT.gt, UScalar.lt_equiv, hcast, hval] at hgt
      simp only [WP.spec_ok]
      split
      · omega
      · rfl
    · rename_i hgt
      simp only [GT.gt, UScalar.lt_equiv, hcast, hval, not_lt] at hgt
      simp only [WP.spec_ok]
      split
      · rfl
      · omega

theorem u32_max_val : core.num.U32.MAX.val = U32.max := by
  simp [core.num.U32.MAX, U32.rMax, U32.max, U32.numBits]

/-- The iterator `derive` and `verify` build, before block 1. -/
theorem zipAt_start (L : Nat) (n : Usize) (len : Usize) (hl : len.val = L) :
    ZipAt n.val L 0 ⟨⟨1#u32, core.num.U32.MAX, false⟩, ⟨⟨0#usize, len⟩, n⟩⟩ := by
  refine ⟨u32_max_val, fun _ => rfl, fun h => by simp at h, by simp, hl, rfl⟩

/-- `Rind::derive` writes PBKDF2's output, for an output of at least one
and at most `u32::MAX` blocks, and refuses any other. -/
theorem rind_derive_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a P k)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (salt out : Slice U8) (hm : hmacBlock a + salt.length + 4 ≤ maxInput) :
    high.pbkdf2.Rind.derive k iterations salt out ⦃ r =>
      if 0 < out.length ∧ (out.length + tagLen a - 1) / tagLen a ≤ U32.max then
        r.1 = .Ok () ∧ r.2.length = out.length ∧
          bv r.2.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val out.length
      else r = (.Err .WrongLength, out) ⦄ := by
  obtain ⟨n, hn, hnv⟩ := tagLen_eq a
  have hpos := tagLen_pos a
  have hent := hr.1
  obtain ⟨e, he⟩ := hent
  unfold high.pbkdf2.Rind.derive
  rw [he, bind_ok]
  apply WP.spec_bind (check_len_spec a P k hk (Slice.len out))
  rintro c rfl
  rw [Slice.len_val]
  by_cases hc : 0 < out.length ∧ (out.length + tagLen a - 1) / tagLen a ≤ U32.max
  · simp only [hc, and_self, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (salted_spec a hr P k hk salt (by omega))
    intro salted hs
    rw [key_algorithm_eq hk, bind_ok, hn, bind_ok]
    simp only [core.ops.range.RangeInclusive.new, bind_ok,
      core.iter.traits.iterator.Iterator.step_by.trait_default,
      core.iter.traits.iterator.Iterator.step_by.default,
      core.iter.traits.iterator.Iterator.zip.trait_default,
      core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have h0 : ¬ n.val = 0 := by omega
    simp only [h0, ↓reduceIte, bind_ok]
    have hz := zipAt_start out.length n (Slice.len out) (Slice.len_val out)
    rw [hnv] at hz
    apply WP.spec_bind (derive_loop_spec a hr P k hk salt.val salted hs hm iterations n hnv
      out.length hc.2 _ out 0 hz rfl (by simp [blocksOut]))
    rintro r ⟨hrl, hrb⟩
    simp only [WP.spec_ok]
    exact ⟨trivial, hrl, by rw [hrb, pbkdf2_eq]⟩
  · simp only [hc, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp

/-! ## `Rind::verify` -/

section
variable (T : Nat → List Byte) (n : Nat) (hT : ∀ i, (T (i + 1)).length = n)

include hT in
theorem blocksOut_take_ceil (hn : 0 < n) (L j : Nat) (hj : L ≤ j * n) :
    (blocksOut T j).take L = (blocksOut T ((L + n - 1) / n)).take L := by
  have hK := ceilDiv_le n L j hn hj
  rw [show j = (L + n - 1) / n + (j - (L + n - 1) / n) by omega,
    blocksOut_take T n hT _ _ _ (ceilDiv_ge n _ hn)]

include hT in
/-- The output matches through block `c' + 1` exactly when it matches through
block `c'` and block `c' + 1`, cut to the output, matches its bytes. -/
theorem prefix_eq_step (prev blk : List U8) (c' : Nat) (hoff : c' * n < prev.length)
    (hblk : bv blk = T (c' + 1)) :
    (bv prev).take ((c' + 1) * n) = (blocksOut T (c' + 1)).take prev.length ↔
      ((bv prev).take (c' * n) = (blocksOut T c').take prev.length ∧
        blk.take (min n (prev.length - c' * n)) =
          prev.slice (c' * n) (c' * n + min n (prev.length - c' * n))) := by
  have hOl := blocksOut_length T n hT c'
  have hA : (blocksOut T c').take prev.length = blocksOut T c' :=
    List.take_of_length_le (by rw [hOl]; omega)
  have hR : (blocksOut T (c' + 1)).take prev.length =
      blocksOut T c' ++ bv (blk.take (min n (prev.length - c' * n))) := by
    rw [blocksOut_succ, List.take_append, hOl, hA, bv_take, hblk]
    congr 1
    rw [← List.take_take, List.take_of_length_le (l := List.take _ _)
      (by simp only [List.length_take, hT]; omega)]
  have hL : (bv prev).take ((c' + 1) * n) =
      (bv prev).take (c' * n) ++ bv (prev.slice (c' * n) (c' * n + min n (prev.length - c' * n))) := by
    rw [show (c' + 1) * n = c' * n + n by rw [Nat.add_mul, one_mul], List.take_add, List.slice,
      Nat.add_sub_cancel_left, bv_take, bv, ← List.map_drop]
    congr 1
    by_cases hcase : n ≤ prev.length - c' * n
    · rw [show min n (prev.length - c' * n) = n by omega]
      rfl
    · rw [show min n (prev.length - c' * n) = prev.length - c' * n by omega]
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp [bv])]
      rfl
  rw [hL, hR, hA]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [List.length_take, bv_length, hOl]; omega)
    exact ⟨h1, ((bv_inj _ _).mp h2).symm⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

end

theorem verify_loop_spec (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (P : List Byte) (k : high.hmac.Key) (hk : KeyOf a P k) (salt : List U8)
    (salted : high.hmac.Streaming) (hs : StreamOf a P salt salted)
    (hm : hmacBlock a + salt.length + 4 ≤ maxInput)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (hash_len : Usize) (hhl : hash_len.val = tagLen a) (prev : Slice U8)
    (hK : (prev.length + tagLen a - 1) / tagLen a ≤ U32.max) (it : BlockIter) (i' : Nat)
    (equal : Bool) (hz : ZipAt (tagLen a) prev.length i' it)
    (heq : equal = true ↔ (bv prev.val).take (i' * tagLen a) =
      (blocksOut (pbT (hmacOf a) P (bv salt) iterations.val) i').take prev.length) :
    high.pbkdf2.Rind.verify_loop it k iterations prev salted hash_len equal ⦃ r =>
      r = true ↔ bv prev.val = (blocksOut (pbT (hmacOf a) P (bv salt) iterations.val)
        ((prev.length + tagLen a - 1) / tagLen a)).take prev.length ⦄ := by
  have hn := tagLen_pos a
  have hT : ∀ i, (pbT (hmacOf a) P (bv salt) iterations.val (i + 1)).length = tagLen a :=
    fun i => pbT_length _ _ _ _ (fun x => hmacOf_length a P x hr) _ _
  have hpl : prev.val.length = prev.length := rfl
  unfold high.pbkdf2.Rind.verify_loop
  apply loop.spec_decr_nat (fun x => prev.length - x.1.snd.iter.start.val)
    (fun x => ∃ i', ZipAt (tagLen a) prev.length i' x.1 ∧
      (x.2 = true ↔ (bv prev.val).take (i' * tagLen a) =
        (blocksOut (pbT (hmacOf a) P (bv salt) iterations.val) i').take prev.length))
  · rintro ⟨it, equal⟩ ⟨i', hz, heq⟩
    simp only at hz heq ⊢
    unfold high.pbkdf2.Rind.verify_loop.body
    apply WP.spec_bind (zip_next_spec _ _ i' hn hK it hz)
    rintro ⟨o, it'⟩ ho
    rcases o with _ | ⟨idx, off⟩
    · simp only [WP.uncurry'] at ho
      refine (WP.spec_ok _).mpr ?_
      show equal = true ↔ _
      rw [heq, List.take_of_length_le (by rw [bv_length]; exact ho),
        blocksOut_take_ceil _ _ hT hn _ _ ho]
    · simp only [WP.uncurry'] at ho
      obtain ⟨hidx, hoff, hlt, hz'⟩ := ho
      dsimp only
      apply WP.spec_bind (block_spec a hr P k hk salt salted hs hm iterations idx)
      rintro blk ⟨hbl, hbb⟩
      have hol : (Slice.len prev).val = prev.length := Slice.len_val prev
      step as ⟨i1, hi1⟩
      step as ⟨len, hlen⟩
      step with digest_as_ref_spec blk as ⟨s, hsl, hsb⟩
      step as ⟨s1, hs1v, hs1l⟩
      step as ⟨i2, hi2⟩
      step as ⟨s2, hs2v, hs2l⟩
      apply WP.spec_bind (ct_equal_spec hr.held _ _)
      rintro _ rfl
      have hlenv : len.val = min (tagLen a) (prev.length - i' * tagLen a) := by
        rw [hlen, core.cmp.impls.OrdUsize.min_val, hhl, hi1, hol, hoff]
      have hT1 : bv s.val = pbT (hmacOf a) P (bv salt) iterations.val (i' + 1) := by
        rw [hsb, hbb, hidx]
      have hs1 : s1.val = s.val.take (min (tagLen a) (prev.length - i' * tagLen a)) := by
        rw [hs1v, List.slice, List.drop_zero, Nat.sub_zero, hlenv]
      have hs2 : s2.val = prev.val.slice (i' * tagLen a)
          (i' * tagLen a + min (tagLen a) (prev.length - i' * tagLen a)) := by
        rw [hs2v, hi2, hoff, hlenv]
      try simp only [WP.spec_ok]
      refine ⟨⟨i' + 1, hz', ?_⟩, zipAt_measure _ _ _ _ _ hz hz' hn hlt⟩
      have := prefix_eq_step _ _ hT prev.val s.val i' (by rw [hpl]; exact hlt) hT1
      rw [hpl] at this
      rw [this, Bool.and_eq_true, heq, hs1, hs2, decide_eq_true_iff]
  · exact ⟨i', hz, heq⟩

theorem rind_verify_spec (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (P : List Byte) (k : high.hmac.Key) (hk : KeyOf a P k)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (salt prev : Slice U8) (hm : hmacBlock a + salt.length + 4 ≤ maxInput) :
    high.pbkdf2.Rind.verify k iterations salt prev ⦃ r =>
      r = if prev.length < tagLen a ∨ ¬ (prev.length + tagLen a - 1) / tagLen a ≤ U32.max then
        .Err .WrongLength
      else if bv prev.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val
          prev.length then .Ok ()
      else .Err .BadSignature ⦄ := by
  obtain ⟨n, hn, hnv⟩ := tagLen_eq a
  have hpos := tagLen_pos a
  obtain ⟨e, he⟩ := hr.1
  unfold high.pbkdf2.Rind.verify
  rw [he, bind_ok, key_algorithm_eq hk, bind_ok, hn, bind_ok]
  have hlv : (Slice.len prev).val = prev.length := Slice.len_val prev
  by_cases hs : prev.length < tagLen a
  · have : Slice.len prev < n := by scalar_tac
    simp only [this, ↓reduceIte, hs, true_or, WP.spec_ok]
  have hs' : ¬ Slice.len prev < n := by scalar_tac
  simp only [hs', ↓reduceIte, hs, false_or]
  apply WP.spec_bind (check_len_spec a P k hk (Slice.len prev))
  rintro c rfl
  rw [hlv]
  by_cases hc : (prev.length + tagLen a - 1) / tagLen a ≤ U32.max
  · have hc' : 0 < prev.length ∧ (prev.length + tagLen a - 1) / tagLen a ≤ U32.max :=
      ⟨by omega, hc⟩
    simp only [hc', and_self, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (salted_spec a hr P k hk salt (by omega))
    intro salted hsd
    simp only [core.ops.range.RangeInclusive.new, bind_ok,
      core.iter.traits.iterator.Iterator.step_by.trait_default,
      core.iter.traits.iterator.Iterator.step_by.default,
      core.iter.traits.iterator.Iterator.zip.trait_default,
      core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have h0 : ¬ n.val = 0 := by omega
    simp only [h0, ↓reduceIte, bind_ok]
    have hz := zipAt_start prev.length n (Slice.len prev) hlv
    rw [hnv] at hz
    apply WP.spec_bind (verify_loop_spec a hr P k hk salt.val salted hsd hm iterations n hnv
      prev hc _ 0 true hz (by simp [blocksOut]))
    intro eq heq
    simp only [low.ct.into_public, bind_ok, ← pbkdf2_eq] at heq ⊢
    by_cases hb : eq = true
    · simp only [hb, ↓reduceIte, (heq.mp hb), not_true_eq_false, WP.spec_ok]
    · have : ¬ bv prev.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val
          prev.length := fun h => hb (heq.mpr h)
      simp only [hb, this, Bool.false_eq_true, not_true_eq_false, ↓reduceIte, WP.spec_ok]
  · simp only [hc, not_false_eq_true, ↓reduceIte,
      core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    simp

/-! ## `Secret` -/

/-- `Secret::derive` on rind's loop writes PBKDF2's output, for an output of at
least one and at most `u32::MAX` blocks, and refuses any other. -/
theorem derive_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (P : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a P k)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (salt out : Slice U8) (hm : hmacBlock a + salt.length + 4 ≤ maxInput) :
    high.pbkdf2.Secret.derive (.Rind k) iterations salt out ⦃ r =>
      if 0 < out.length ∧ (out.length + tagLen a - 1) / tagLen a ≤ U32.max then
        r.1 = .Ok () ∧ r.2.length = out.length ∧
          bv r.2.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val out.length
      else r = (.Err .WrongLength, out) ⦄ := by
  unfold high.pbkdf2.Secret.derive
  exact rind_derive_spec a hr P k hk iterations salt out hm

/-- `Secret::verify` on rind's loop accepts exactly PBKDF2's output, of at
least the tag's length and at most `u32::MAX` blocks. -/
theorem verify_spec (a : high.hmac.Algorithm) (hr : RunsHmac a)
    (P : List Byte) (k : high.hmac.Key) (hk : KeyOf a P k)
    (iterations : core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
    (salt prev : Slice U8) (hm : hmacBlock a + salt.length + 4 ≤ maxInput) :
    high.pbkdf2.Secret.verify (.Rind k) iterations salt prev ⦃ r =>
      r = if prev.length < tagLen a ∨ ¬ (prev.length + tagLen a - 1) / tagLen a ≤ U32.max then
        .Err .WrongLength
      else if bv prev.val = pbkdf2 (hmacOf a) (tagLen a) P (bv salt.val) iterations.val
          prev.length then .Ok ()
      else .Err .BadSignature ⦄ := by
  unfold high.pbkdf2.Secret.verify
  exact rind_verify_spec a hr P k hk iterations salt prev hm

end rind.x86_64.kdf
