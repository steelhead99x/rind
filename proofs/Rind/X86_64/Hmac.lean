import Rind.X86_64.Sha
import Rind.X86_64.HmacDispatch
open Aeneas Aeneas.Std Result rind.spec

/-!
# HMAC's keyed states, `high::hmac`, over any hash

`HmacKey` and `Hmac` compute RFC 2104's HMAC, as HACL*'s `Spec.Agile.HMAC`
states it, over any hash whose `Hash` impl meets `HashSpec`: SHA-1's and
SHA-256's do, given `Sha1Blocks` and `Sha256Blocks`.
-/

namespace rind.x86_64

/-- `S` with every byte from index `i` on XORed with `c`. -/
def xorFrom (c : U8) (S : Slice U8) (i : Nat) : Slice U8 :=
  Slice.from (S.val.mapIdx fun j x => if i ≤ j then x ^^^ c else x) (by simp)

theorem xorFrom_step (c : U8) (S : Slice U8) (i : Nat) (hi : i < S.length) :
    (xorFrom c S (i + 1)).setAtNat i (S.val[i] ^^^ c) = xorFrom c S i := by
  simp only [Slice.setAtNat, xorFrom, Slice.from_val]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_set]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h, List.getElem_mapIdx, List.getElem_mapIdx]
    by_cases hj : i + 1 ≤ j
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right (by omega)]

theorem xorFrom_end (c : U8) (S : Slice U8) : xorFrom c S S.length = S := by
  apply Slice.ext
  simp only [xorFrom, Slice.from_val]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_mapIdx, ite_eq_right (by simp only [List.length_mapIdx, Slice.length] at h1 ⊢; omega)]

theorem new_loop0_spec (S : Slice U8)
    (back : core.slice.iter.IterMut U8 → core.slice.iter.IterMut U8) :
    high.hmac.HmacKey.new_loop0 { slice := S } back ⦃ r =>
      r = back ⟨xorFrom 54#u8 S 0, S.length⟩ ⦄ := by
  unfold high.hmac.HmacKey.new_loop0
  apply loop.spec_decr_nat (fun x => S.length - x.1.i)
    (fun x => x.1.slice = S ∧ x.1.i ≤ S.length ∧
      x.2 ⟨xorFrom 54#u8 S x.1.i, S.length⟩ = back ⟨xorFrom 54#u8 S 0, S.length⟩)
  · rintro ⟨⟨sl, i⟩, bk⟩ ⟨hs, hi, hb⟩
    simp only at hs hi hb ⊢
    subst hs
    unfold high.hmac.HmacKey.new_loop0.body core.slice.iter.IteratorIterMut.next
    split
    · rename_i hlt
      have hlt' : i < sl.length := by simpa [Slice.len, Slice.length] using hlt
      step*
      have hb1 : byte1 = sl.val[i] ^^^ 54#u8 := UScalar.eq_of_val_eq byte1_post
      refine ⟨by omega, ?_, by omega⟩
      rw [hb1, xorFrom_step 54#u8 sl i hlt', hb]
    · rename_i hge
      have hl : sl.length = sl.val.length := rfl
      have hi' : i = sl.length := by simp [Slice.len] at hge; omega
      step*
      subst hi'
      rw [xorFrom_end] at hb
      exact hb
  · exact ⟨rfl, by simp, rfl⟩

theorem new_loop1_spec (S : Slice U8)
    (back : core.slice.iter.IterMut U8 → core.slice.iter.IterMut U8) :
    high.hmac.HmacKey.new_loop1 { slice := S } back ⦃ im b =>
      b im = back ⟨xorFrom (92#u8 ^^^ 54#u8) S 0, S.length⟩ ⦄ := by
  unfold high.hmac.HmacKey.new_loop1
  apply loop.spec_decr_nat (fun x => S.length - x.1.i)
    (fun x => x.1.slice = S ∧ x.1.i ≤ S.length ∧
      x.2 ⟨xorFrom (92#u8 ^^^ 54#u8) S x.1.i, S.length⟩ =
        back ⟨xorFrom (92#u8 ^^^ 54#u8) S 0, S.length⟩)
  · rintro ⟨⟨sl, k⟩, bk⟩ ⟨hs, hi, hb⟩
    simp only at hs hi hb ⊢
    subst hs
    unfold high.hmac.HmacKey.new_loop1.body core.slice.iter.IteratorIterMut.next
    split
    · rename_i hlt
      have hlt' : k < sl.length := by simpa [Slice.len, Slice.length] using hlt
      step*
      have hc : i = 92#u8 ^^^ 54#u8 := UScalar.eq_of_val_eq i_post
      have hb1 : byte1 = sl.val[k] ^^^ (92#u8 ^^^ 54#u8) := by
        rw [← hc]; exact UScalar.eq_of_val_eq byte1_post
      refine ⟨by omega, ?_, by omega⟩
      rw [hb1, xorFrom_step _ sl k hlt', hb]
    · rename_i hge
      have hl : sl.length = sl.val.length := rfl
      have hi' : k = sl.length := by simp [Slice.len] at hge; omega
      step*
      subst hi'
      rw [xorFrom_end] at hb
      exact hb
  · exact ⟨rfl, by simp, rfl⟩

@[step]
theorem hashBlock_deref_spec (hb : high.hash.HashBlock) (h : hb.len.val ≤ 128) :
    high.hash.HashBlock.Insts.CoreOpsDerefDerefSliceU8.deref hb ⦃ s =>
      s.val = hb.buf.val.take hb.len.val ⦄ := by
  unfold high.hash.HashBlock.Insts.CoreOpsDerefDerefSliceU8.deref
  step*
  simp_all [List.slice]

@[step]
theorem hashBlock_deref_mut_spec (hb : high.hash.HashBlock) (h : hb.len.val ≤ 128) :
    high.hash.HashBlock.Insts.CoreOpsDerefDerefMutSliceU8.deref_mut hb ⦃ s back =>
      s.val = hb.buf.val.take hb.len.val ∧ ∀ s' : Slice U8, s'.length = hb.len.val →
        (back s').len = hb.len ∧ (back s').buf.val.take hb.len.val = s'.val ⦄ := by
  unfold high.hash.HashBlock.Insts.CoreOpsDerefDerefMutSliceU8.deref_mut
  step*
  refine ⟨by simp_all [List.slice], fun s' hs' => ?_⟩
  have hbl : hb.buf.val.length = 128 := by simp
  rw [s_post2, setSlice!_eq _ _ _ (by simp only [Slice.length] at hs'; omega)]
  simp only [List.take_zero, List.nil_append, Nat.zero_add]
  rw [List.take_left' (by simp only [Slice.length] at hs'; omega)]

theorem bv_xorFrom (c : U8) (S : Slice U8) :
    bv (xorFrom c S 0).val = (bv S.val).map (· ^^^ c.bv) := by
  simp only [xorFrom, Slice.from_val, bv]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_mapIdx, List.getElem_map, Nat.zero_le, ↓reduceIte]
  rfl

theorem xor_pads (x : BitVec UScalarTy.U8.numBits) :
    x ^^^ (54#u8).bv ^^^ (92#u8 ^^^ 54#u8).bv = x ^^^ 0x5c := by
  rw [BitVec.xor_assoc]
  congr 1

section
variable {Self C S : Type} {inst : high.hash.Hash Self C S} {H : List Byte → List Byte}
  {B L max : Nat} {Abs : List U8 → S → Prop} {CAbs : List U8 → C → Prop}

theorem HashSpec.hash_spec (hs : HashSpec inst H B L max Abs CAbs) (m : Slice U8)
    (hm : m.length ≤ max) :
    inst.hash m ⦃ d => outLen d.algorithm = L ∧ digestBytes d = H (bv m.val) ⦄ := by
  rw [hs.hash_default]
  unfold high.hash.Hash.hash.default
  apply WP.spec_bind hs.initial
  intro s0 h0
  have := hs.finish_with [] s0 m h0 (by simpa using hm)
  simpa using this

/-- HACL*'s `Spec.Agile.HMAC.wrap`: a key longer than a block hashed, then
zero-padded to a block. -/
def keyBlock (H : List Byte → List Byte) (B : Nat) (key : List Byte) : List Byte :=
  let key := if key.length ≤ B then key else H key
  key ++ List.replicate (B - key.length) 0

/-- `k`'s keyed states have absorbed `key`'s block XOR HMAC's two pads. -/
def HmacKeyed (Abs : List U8 → S → Prop) (H : List Byte → List Byte) (B : Nat)
    (key : List Byte) {Self C : Type} (k : high.hmac.HmacKey Self C S) : Prop :=
  ∃ ki ko : List U8, Abs ki k.inner ∧ Abs ko k.outer ∧
    bv ki = (keyBlock H B key).map (· ^^^ 0x36) ∧ bv ko = (keyBlock H B key).map (· ^^^ 0x5c)

theorem hmac_key_new_spec (hs : HashSpec inst H B L max Abs CAbs) (key : Slice U8)
    (hk : key.length ≤ max) :
    high.hmac.HmacKey.new inst key ⦃ k => HmacKeyed Abs H B (bv key.val) k ⦄ := by
  obtain ⟨hLB, hL64, hB128, hBmax, hHL⟩ := hs.out
  unfold high.hmac.HmacKey.new
  apply WP.spec_bind hs.zeroed_block
  rintro kb ⟨hkb1, hkb2⟩
  step*
  have hkl : key.len.val = key.length := by simp [Slice.len, Slice.length]
  have hkl' : key.len.val = key.val.length := hkl
  have hsl : s.len.val = B := by
    simp only [Slice.len]; simp [s_post, hkb1, hkb2]; omega
  apply WP.spec_bind (Pₘ := fun (kb1 : high.hash.HashBlock) => kb1.len.val = B ∧
    bv (kb1.buf.val.take B) = keyBlock H B (bv key.val))
  · split
    · rename_i hgt
      have hgt' : B < key.length := by simp only [GT.gt, UScalar.lt_equiv] at hgt; omega
      apply WP.spec_bind (hs.hash_spec key hk)
      rintro hkey ⟨hk1, hk2⟩
      step*
      step with digest_as_ref_spec hkey as ⟨s2, hs2l, hs2b⟩
      step*
      have hs1 : s1.val = List.replicate B 0#u8 := by
        rw [s1_post, hkb1, hkb2, List.take_replicate, Nat.min_eq_left hB128]
      have hs2l' : s2.val.length = L := by rw [← hk1]; exact hs2l
      have hX : (index_mut_back s4).val = s2.val ++ List.replicate (B - L) 0#u8 := by
        rw [s3_post2, s4_post, hs1, setSlice!_eq _ _ _ (by simp; omega)]
        simp only [List.take_zero, List.nil_append, Nat.zero_add, List.drop_replicate, hs2l']
      obtain ⟨h1, h2⟩ := s1_post1 (index_mut_back s4)
        (by show (index_mut_back s4).val.length = _; rw [hX, hkb1]; simp; omega)
      rw [hkb1] at h2
      refine ⟨by rw [h1, hkb1], ?_⟩
      rw [h2, hX]
      simp only [keyBlock, bv, List.map_append, List.map_replicate, List.length_map]
      rw [ite_eq_right (by simp only [GT.gt, UScalar.lt_equiv] at hgt; omega)]
      have : List.map (fun x => x.bv) s2.val = H (List.map (fun x => x.bv) key.val) := by
        simp only [bv] at hk2 hs2b; rw [hs2b, hk2]
      rw [this, hHL]
      try rfl
    · rename_i hle
      have hle' : key.val.length ≤ B := by simp only [GT.gt, UScalar.lt_equiv] at hle; omega
      step*
      have hs1 : s1.val = List.replicate B 0#u8 := by
        rw [s1_post, hkb1, hkb2, List.take_replicate, Nat.min_eq_left hB128]
      have hX : (index_mut_back s3).val = key.val ++ List.replicate (B - key.length) 0#u8 := by
        rw [s2_post2, s3_post, hs1, setSlice!_eq _ _ _ (by simp; omega)]
        simp only [List.take_zero, List.nil_append, Nat.zero_add, List.drop_replicate]
      obtain ⟨h1, h2⟩ := s1_post1 (index_mut_back s3)
        (by show (index_mut_back s3).val.length = _; rw [hX, hkb1]; simp; omega)
      rw [hkb1] at h2
      refine ⟨by rw [h1, hkb1], ?_⟩
      rw [h2, hX]
      simp only [keyBlock, bv, List.map_append, List.map_replicate, List.length_map]
      rw [ite_eq_left hle', List.length_map]
      rfl
  · rintro kb1 ⟨hkb1', hkb1''⟩
    simp only [core.slice.Slice.iter_mut, bind_ok]
    step*
    have hs1l : s1.val.length = B := by
      rw [s1_post, hkb1', List.length_take]; simp; omega
    have hxl : ∀ c, (xorFrom c s1 0).length = kb1.len.val := by
      intro c; simp only [xorFrom, Slice.length, Slice.from_val, List.length_mapIdx]; omega
    step with new_loop0_spec s1 (fun im => im) as ⟨bk, hbk⟩
    apply WP.spec_bind hs.initial
    intro inner hinner
    obtain ⟨h1, h2⟩ := s1_post1 bk.slice (by rw [hbk]; exact hxl _)
    step*
    have hs3 : s3.val = (xorFrom 54#u8 s1 0).val := by rw [s3_post, h1, h2, hbk]
    have hs3l : s3.length = B := by
      simp only [Slice.length]; rw [hs3]; have := hxl 54#u8; simp only [Slice.length] at this; omega
    apply WP.spec_bind (hs.update_blocks [] inner s3 hinner (by rw [hs3l, Nat.mod_self])
      (by simp only [List.length_nil]; omega))
    intro inner1 hinner1
    step*
    have hs4 : s4.val = (xorFrom 54#u8 s1 0).val := by rw [s4_post, h1, h2, hbk]
    have hs4l : s4.length = kb1.len.val := by
      simp only [Slice.length]; rw [hs4]; have := hxl 54#u8; simp only [Slice.length] at this; omega
    step with new_loop1_spec s4 (fun im => im) as ⟨im, b1, hb1⟩
    obtain ⟨h1', h2'⟩ := s4_post1 (b1 im).slice (by
      rw [hb1]; simp only [xorFrom, Slice.length, Slice.from_val, List.length_mapIdx]
      rw [h1]; simp only [Slice.length] at hs4l; exact hs4l)
    step*
    have hs6 : s6.val = (xorFrom (92#u8 ^^^ 54#u8) s4 0).val := by
      rw [s6_post, h1', h2', hb1]
    have hs6l : s6.length = B := by
      simp only [Slice.length]; rw [hs6]; simp only [xorFrom, Slice.from_val, List.length_mapIdx]
      simp only [Slice.length] at hs4l; omega
    apply WP.spec_bind (hs.update_blocks [] inner s6 hinner (by rw [hs6l, Nat.mod_self])
      (by simp only [List.length_nil]; omega))
    intro outer houter
    simp only [WP.spec_ok]
    have hK : bv s1.val = keyBlock H B (bv key.val) := by rw [s1_post, hkb1']; exact hkb1''
    refine ⟨s3.val, s6.val, by simpa using hinner1, by simpa using houter, ?_, ?_⟩
    · rw [hs3, bv_xorFrom, hK]; rfl
    · rw [hs6, bv_xorFrom, hs4, bv_xorFrom, hK, List.map_map]
      congr 1
      funext x
      exact xor_pads x

theorem keyBlock_length (hs : HashSpec inst H B L max Abs CAbs) (key : List Byte) :
    (keyBlock H B key).length = B := by
  obtain ⟨hLB, -, -, -, hHL⟩ := hs.out
  unfold keyBlock
  split <;> simp [hHL] <;> omega

theorem hmac_def (key text : List Byte) :
    hmac H B key text = H ((keyBlock H B key).map (· ^^^ 0x5c) ++
      H ((keyBlock H B key).map (· ^^^ 0x36) ++ text)) := rfl

/-- The tag of `message` under the key `k` holds is HMAC's. -/
theorem hmac_sign_spec (hs : HashSpec inst H B L max Abs CAbs) (key : List Byte)
    (k : high.hmac.HmacKey Self C S) (hk : HmacKeyed Abs H B key k) (m : Slice U8)
    (hm : B + m.length ≤ max) :
    high.hmac.HmacKey.sign inst k m ⦃ d =>
      outLen d.algorithm = L ∧ digestBytes d = hmac H B key (bv m.val) ⦄ := by
  obtain ⟨ki, ko, hi, ho, hbi, hbo⟩ := hk
  obtain ⟨hLB, hL64, -, hBmax, -⟩ := hs.out
  have hkil : ki.length = B := by
    have := congrArg List.length hbi; simp [bv, keyBlock_length hs] at this; exact this
  have hkol : ko.length = B := by
    have := congrArg List.length hbo; simp [bv, keyBlock_length hs] at this; exact this
  unfold high.hmac.HmacKey.sign
  apply WP.spec_bind (hs.finish_with ki k.inner m hi (by omega))
  rintro d1 ⟨hd1l, hd1⟩
  -- After a long inner, the outer hash may stay on the long compressor so a
  -- 16 KiB I-cache is not evicted. Both paths compute the same digest.
  apply WP.spec_bind (hs.finish_uses_long m)
  intro b _
  have outer : ∀ fin : S → Slice U8 → Result high.digest.Digest,
      (∀ (p : List U8) (st : S) (msg : Slice U8), Abs p st → p.length + msg.length ≤ max →
        fin st msg ⦃ d => outLen d.algorithm = L ∧ digestBytes d = H (bv (p ++ msg.val)) ⦄) →
      (do
        let s ← high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d1
        fin k.outer s) ⦃ d =>
          outLen d.algorithm = L ∧ digestBytes d = hmac H B key (bv m.val) ⦄ := by
    intro fin hfin
    step with digest_as_ref_spec d1 as ⟨s, hsl, hsb⟩
    apply WP.spec_mono (hfin ko k.outer s ho (by omega))
    rintro d ⟨hdl, hd⟩
    refine ⟨hdl, ?_⟩
    rw [hd, hmac_def, ← hbo, ← hbi]
    simp only [bv, List.map_append] at hsb hd1 ⊢
    rw [hsb, hd1]
  split
  · exact outer _ hs.finish_with_after_long
  · exact outer _ hs.finish_with

/-- `h` is a tag computation under `key` that has been given `p`. -/
def HmacCtx (CAbs : List U8 → C → Prop) (Abs : List U8 → S → Prop) (H : List Byte → List Byte)
    (B : Nat) (key : List Byte) (p : List U8) {Self : Type} (h : high.hmac.Hmac Self C S) : Prop :=
  ∃ ki ko : List U8, CAbs (ki ++ p) h.inner ∧ Abs ko h.outer ∧ ki.length = B ∧ ko.length = B ∧
    bv ki = (keyBlock H B key).map (· ^^^ 0x36) ∧ bv ko = (keyBlock H B key).map (· ^^^ 0x5c)

theorem hmac_start_spec (hs : HashSpec inst H B L max Abs CAbs) (key : List Byte)
    (k : high.hmac.HmacKey Self C S) (hk : HmacKeyed Abs H B key k) :
    high.hmac.HmacKey.start inst k ⦃ h => HmacCtx CAbs Abs H B key [] h ⦄ := by
  obtain ⟨ki, ko, hi, ho, hbi, hbo⟩ := hk
  have hkil : ki.length = B := by
    have := congrArg List.length hbi; simp [bv, keyBlock_length hs] at this; exact this
  have hkol : ko.length = B := by
    have := congrArg List.length hbo; simp [bv, keyBlock_length hs] at this; exact this
  unfold high.hmac.HmacKey.start
  apply WP.spec_bind (hs.resume ki k.inner hi)
  intro c hc
  apply WP.spec_bind (hs.clone ko k.outer ho)
  intro o hoc
  simp only [WP.spec_ok]
  exact ⟨ki, ko, by simpa using hc, hoc, hkil, hkol, hbi, hbo⟩

theorem hmac_update_spec (hs : HashSpec inst H B L max Abs CAbs) (key : List Byte) (p : List U8)
    {T : Type} (asRef : core.convert.AsRef T (Slice U8)) (h : high.hmac.Hmac Self C S)
    (hh : HmacCtx CAbs Abs H B key p h) (bytes : T) (b : Slice U8)
    (hb : asRef.as_ref bytes = ok b) (hm : B + p.length + b.length ≤ max) :
    high.hmac.Hmac.update inst asRef h bytes ⦃ h' => HmacCtx CAbs Abs H B key (p ++ b.val) h' ⦄ := by
  obtain ⟨ki, ko, hi, ho, hkil, hkol, hbi, hbo⟩ := hh
  unfold high.hmac.Hmac.update
  rw [hb, bind_ok]
  apply WP.spec_bind (hs.update (ki ++ p) h.inner b hi (by
    simp only [Slice.length] at hm ⊢; simp only [List.length_append]; omega))
  intro c hc
  simp only [WP.spec_ok]
  exact ⟨ki, ko, by simpa using hc, ho, hkil, hkol, hbi, hbo⟩

theorem hmac_finish_spec (hs : HashSpec inst H B L max Abs CAbs) (key : List Byte) (p : List U8)
    (h : high.hmac.Hmac Self C S) (hh : HmacCtx CAbs Abs H B key p h) (hm : B + p.length ≤ max) :
    high.hmac.Hmac.finish inst h ⦃ d =>
      outLen d.algorithm = L ∧ digestBytes d = hmac H B key (bv p) ⦄ := by
  obtain ⟨ki, ko, hi, ho, hkil, hkol, hbi, hbo⟩ := hh
  obtain ⟨hLB, hL64, -, hBmax, -⟩ := hs.out
  unfold high.hmac.Hmac.finish
  apply WP.spec_bind (hs.finish (ki ++ p) h.inner hi (by simp; omega))
  rintro d1 ⟨hd1l, hd1⟩
  step with digest_as_ref_spec d1 as ⟨s, hsl, hsb⟩
  apply WP.spec_mono (hs.finish_with ko h.outer s ho (by omega))
  rintro d ⟨hdl, hd⟩
  refine ⟨hdl, ?_⟩
  rw [hd, hmac_def, ← hbo, ← hbi]
  simp only [bv, List.map_append] at hsb hd1 ⊢
  rw [hsb, hd1]

theorem hmac_clone_spec (hs : HashSpec inst H B L max Abs CAbs) (key : List Byte) (p : List U8)
    (h : high.hmac.Hmac Self C S) (hh : HmacCtx CAbs Abs H B key p h) :
    high.hmac.Hmac.Insts.CoreCloneClone.clone inst h ⦃ h' => HmacCtx CAbs Abs H B key p h' ⦄ := by
  obtain ⟨ki, ko, hi, ho, hkil, hkol, hbi, hbo⟩ := hh
  unfold high.hmac.Hmac.Insts.CoreCloneClone.clone
  apply WP.spec_bind (hs.cclone _ _ hi)
  intro c hc
  apply WP.spec_bind (hs.clone _ _ ho)
  intro o hoc
  simp only [WP.spec_ok]
  exact ⟨ki, ko, hc, hoc, hkil, hkol, hbi, hbo⟩

end

/-! ## SHA-1, SHA-256, and HMAC over them -/

/-- SHA-256 of a message is FIPS 180-4's, given the block functions' contracts. -/
theorem sha256_hash (hb : Sha256Blocks) (m : Slice U8) (hm : m.length ≤ maxInput) :
    Sha256Hash.hash m ⦃ d => digestBytes d = sha256.hash (bv m.val) ⦄ :=
  WP.spec_mono ((sha256_hashSpec hb).hash_spec m hm) fun _ h => h.2

/-- SHA-1 of a message is FIPS 180-4's, given the block functions' contracts. -/
theorem sha1_hash (hb : Sha1Blocks) (m : Slice U8) (hm : m.length ≤ maxInput) :
    Sha1Hash.hash m ⦃ d => digestBytes d = sha1.hash (bv m.val) ⦄ :=
  WP.spec_mono ((sha1_hashSpec hb).hash_spec m hm) fun _ h => h.2

/-- HMAC-SHA256's tag of `m` under `key` is RFC 2104's, given the block
functions' contracts. -/
theorem hmac_sha256_sign (hb : Sha256Blocks) (key m : Slice U8) (hk : key.length ≤ maxInput)
    (hm : 64 + m.length ≤ maxInput) :
    (do
      let k ← high.hmac.HmacKey.new Sha256Hash key
      high.hmac.HmacKey.sign Sha256Hash k m) ⦃ d =>
      digestBytes d = hmac sha256.hash 64 (bv key.val) (bv m.val) ⦄ := by
  apply WP.spec_bind (hmac_key_new_spec (sha256_hashSpec hb) key hk)
  intro k hk'
  exact WP.spec_mono (hmac_sign_spec (sha256_hashSpec hb) _ k hk' m hm) fun _ h => h.2

/-- HMAC-SHA1's tag of `m` under `key` is RFC 2104's, given the block
functions' contracts. -/
theorem hmac_sha1_sign (hb : Sha1Blocks) (key m : Slice U8) (hk : key.length ≤ maxInput)
    (hm : 64 + m.length ≤ maxInput) :
    (do
      let k ← high.hmac.HmacKey.new Sha1Hash key
      high.hmac.HmacKey.sign Sha1Hash k m) ⦃ d =>
      digestBytes d = hmac sha1.hash 64 (bv key.val) (bv m.val) ⦄ := by
  apply WP.spec_bind (hmac_key_new_spec (sha1_hashSpec hb) key hk)
  intro k hk'
  exact WP.spec_mono (hmac_sign_spec (sha1_hashSpec hb) _ k hk' m hm) fun _ h => h.2

end rind.x86_64
