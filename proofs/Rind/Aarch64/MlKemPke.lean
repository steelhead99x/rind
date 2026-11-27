import Rind.Aarch64.MlKemPoly
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem rind.spec.s2n

/-!
# K-PKE on aarch64

`mid::mlkem`'s K-PKE for ML-KEM-768, over `MlKemPoly`'s vector specs. The
translation takes the set's `Params` impl as a parameter, since Aeneas does
not translate it: `Is768` states what ML-KEM-768's impl is.
-/

namespace rind.aarch64

namespace MlKemPke

open MlKemCoding MlKemRoutines MlKemGeneric MlKemPoly

abbrev Vec := Std.Array Poly 3#usize
abbrev Mat := Std.Array Poly 9#usize
abbrev Cache := Std.Array (Std.Array I16 128#usize) 3#usize
abbrev Enc := Std.Array (Std.Array U8 384#usize) 3#usize
abbrev EkBytes := Std.Array U8 1184#usize
abbrev CtBytes := Std.Array U8 1088#usize
abbrev DkBytes := Std.Array U8 2400#usize

/-- `P` is ML-KEM-768's `Params` impl: its constants, and its types'
`FixedArray` impls those of arrays. -/
structure Is768 {X : Type} (P : mid.mlkem.Params X Vec Mat EkBytes CtBytes DkBytes Cache Enc) : Prop where
  K : P.K = ok 3#usize
  ETA1 : P.ETA1 = ok 2#usize
  DU : P.DU = ok 10#usize
  DV : P.DV = ok 4#usize
  vec : IsArray P.VectorInst.FixedArraySelfArrayI16256Inst
  cache : IsArray P.VectorInst.FixedArraySelf_MulCacheArrayI16128Inst
  enc : IsArray P.VectorInst.FixedArraySelf_EncodedArrayU8384Inst
  mat : IsArray P.FixedArraySelf_MatrixArrayI16256Inst
  ek : IsArray P.FixedArraySelf_EncapKeyBytesU8Inst
  ct : IsArray P.FixedArraySelf_CiphertextBytesU8Inst
  dk : IsArray P.FixedArraySelf_DecapKeyBytesU8Inst

theorem Holds.mono {lo hi lo' hi' : ℤ} {n : ℕ} {a : List I16} {F : Polynomial} (h : Holds lo hi n a F)
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : Holds lo' hi' n a F :=
  fun p hp => ⟨le_trans h1 (h p hp).1, le_trans (h p hp).2.1 h2, (h p hp).2.2⟩

/-- `len` bytes of `l` from `off`. -/
abbrev sub (l : List U8) (off len : ℕ) : List U8 := (l.drop off).take len

theorem sub_length (l : List U8) (off len : ℕ) (h : off + len ≤ l.length) : (sub l off len).length = len := by
  simp only [sub, List.length_take, List.length_drop]
  omega

/-- `Decompress_10(ByteDecode_10)` of polynomial `j` of `u`'s first 960 bytes. -/
def decompU (u : List U8) (hu : 960 ≤ u.length) (j : ℕ) : Polynomial :=
  if hj : j < 3 then
    Polynomial.Decompress 10 (ByteDecode (toVec (32 * 10) (sub u (320 * j) 320) (sub_length _ _ _ (by omega))))
  else 0

/-- `Decompress_4(ByteDecode_4)` of `v`'s 128 bytes. -/
def decompV (c : List U8) (hc : c.length = 1088) : Polynomial :=
  Polynomial.Decompress 4 (ByteDecode (toVec (32 * 4) (sub c 960 128) (sub_length _ _ _ (by omega))))

/-- `K-PKE.Decrypt`'s `w`, as rind computes it. -/
def decrypt (dk : Enc) (c : List U8) (hc : c.length = 1088) : Polynomial :=
  decompV c hc - NTTInv (dot3 (fun j => decode12 (dk.val[j]!)) (fun j => NTT (decompU c (by omega) j)))

theorem decompress_vector_loop_spec (bytes : Slice U8) (hb : 960 ≤ bytes.val.length) (polys : Slice Poly)
    (hl : polys.length = 3) (it : core.ops.range.Range Usize) (hs : it.start.val = 0) (he : it.end.val = 3) :
    mid.mlkem.decompress_vector_loop 10#usize 320#usize it bytes polys ⦃ y => y.length = 3 ∧
      ∀ j < 3, Holds 0 3328 256 (y.val[j]!).val (decompU bytes.val hb j) ⦄ := by
  unfold mid.mlkem.decompress_vector_loop
  apply WP.spec_mono (slice_loop (α := Poly) 3 (fun _ _ _ => True)
    (fun j _ b => Holds 0 3328 256 b.val (decompU bytes.val hb j)) _ ?_ polys hl (fun _ _ => trivial) it hs he)
  · intro y hy
    exact hy
  · intro it s he hs hl _
    simp only
    unfold mid.mlkem.decompress_vector_loop.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s1, hs1, hsl⟩
      have hs1l : s1.val.length = (320#usize).val := by
        show s1.length = _
        rw [hsl, hi2, hi1]
        scalar_tac
      rw [try_from_ok 320#usize s1 hs1l]
      simp only [core.result.Result.unwrap]
      step as ⟨a, back', ha, hb'⟩
      subst hb'
      step with decompress_spec 10#usize (L := 320#usize) (by decide) (by decide) (Std.Array.from (n := 320#usize) s1.val hs1l) a
        as ⟨a2, ha2⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, by rw [set_length]; exact hl, ?_,
        fun j hj => set_getElem!_ne _ _ _ _ hj⟩
      rw [set_getElem!_self _ _ _ (by omega)]
      have hv : s1.val = sub bytes.val (320 * it.start.val) 320 := by
        rw [hs1, hi1, hi2]
        simp only [sub, List.slice]
        congr 1
        scalar_tac
      unfold decompU
      rw [dite_true' (by omega)]
      convert ha2 using 4
      · rfl
      · rfl
      · rw [Std.Array.from_val, hv]
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      exact ⟨by omega, rfl⟩

theorem kpke_decrypt_spec {X : Type} (P : mid.mlkem.Params X Vec Mat EkBytes CtBytes DkBytes Cache Enc)
    (hP : Is768 P) (key : mid.mlkem.DecapKey X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (c : CtBytes) :
    mid.mlkem.DecapKey.kpke_decrypt P key c ⦃ m =>
      toVec (32 * 1) m.val m.property =
        ByteEncode 1 (Polynomial.Compress 1 (decrypt key.dk_pke c.val c.property)) ⦄ := by
  unfold mid.mlkem.DecapKey.kpke_decrypt
  simp only [hP.ct.as_ref, hP.DU, hP.K, hP.DV, zero_eq _ hP.vec, zero1_eq, hP.vec.as_mut]
  step as ⟨s, hs⟩
  have h10 : (10#usize).val = 10 := rfl
  have h4 : (4#usize).val = 4 := rfl
  simp only [h10, h4]
  step as ⟨i1, hi1⟩
  step as ⟨i3, hi3⟩
  have hsl : s.length = 1088 := by show s.val.length = _; rw [hs]; exact c.property
  step as ⟨c_1, c_2, hl1, hl2, hv1, hv2⟩
  have hc1l : c_1.length = 960 := by rw [hl1, hi3, hi1]
  have hc1 : 960 ≤ c_1.val.length := by
    show 960 ≤ c_1.length
    omega
  apply spec_bind_ok
  refine WP.spec_bind (Pₘ := fun (r : mid.mlkem.Coeffs Vec mid.mlkem.Normal) =>
    VHolds 0 3328 3 r.1.val (decompU c_1.val hc1)) ?_ ?_
  · generalize Std.Array.repeat 3#usize (Std.Array.repeat 256#usize 0#i16) = z0
    show (do
      let (s1, as_mut_back) ← Array.Insts.CoreConvertAsMutSlice.as_mut z0
      let s2 ← mid.mlkem.decompress_vector 10#usize 320#usize c_1 s1
      ok ((as_mut_back s2, ()) : mid.mlkem.Coeffs Vec mid.mlkem.Normal)) ⦃ _ ⦄
    simp only [Array.Insts.CoreConvertAsMutSlice.as_mut]
    unfold mid.mlkem.decompress_vector
    apply spec_bind_ok
    refine WP.spec_bind (decompress_vector_loop_spec c_1 hc1 _ ?_ _ ?_ ?_) ?_
    · simp [Slice.length]
    · rfl
    · show (Slice.len _).val = 3
      rw [Slice.len_val]
      simp [Slice.length]
    intro s2 ⟨hl2', hq2⟩
    apply (WP.spec_ok _).2
    have hl2'' : s2.length = (3#usize).val := hl2'
    beta_reduce
    rw [dite_true' hl2'']
    intro j hj
    rw [Std.Array.from_val]
    exact hq2 j hj
  intro u hu
  obtain ⟨u, upd⟩ := u
  generalize Std.Array.repeat 256#usize 0#i16 = z1
  have hc2l : c_2.val.length = (128#usize).val := by
    show c_2.length = _
    rw [hl2, hsl, hi3, hi1]
    rfl
  have hcl : c.val.length = 1088 := c.property
  have hc2v : c_2.val = sub c.val 960 128 := by
    rw [hv2, hi3, hi1, hs]
    simp only [sub]
    rw [List.take_of_length_le (by rw [List.length_drop]; omega)]
  rw [try_from_ok 128#usize c_2 hc2l]
  apply spec_bind_ok
  apply spec_bind_ok
  apply spec_bind_ok
  refine WP.spec_bind (Pₘ := fun (r : mid.mlkem.Coeffs (Std.Array I16 256#usize) mid.mlkem.Normal) =>
    Holds 0 3328 256 r.1.val (decompV c.val c.property)) ?_ ?_
  · show (do
      let a3 ← mid.mlkem.decompress 4#usize (Std.Array.from c_2.val hc2l) z1
      ok ((a3, ()) : mid.mlkem.Coeffs (Std.Array I16 256#usize) mid.mlkem.Normal)) ⦃ _ ⦄
    apply WP.spec_bind (decompress_spec 4#usize (L := 128#usize) (by decide) (by decide)
      (Std.Array.from c_2.val hc2l) z1)
    intro a3 ha3
    apply (WP.spec_ok _).2
    unfold decompV
    convert ha3 using 4
    · rfl
    · rfl
    · rw [Std.Array.from_val, hc2v]
  intro a ha
  obtain ⟨a, pda⟩ := a
  apply WP.spec_bind (from_bytes_spec P.VectorInst hP.vec hP.enc key.dk_pke)
  intro sh hsh
  obtain ⟨sh, pds⟩ := sh
  apply WP.spec_bind (ntt_spec _ hP.vec u (decompU c_1.val hc1)
    (fun j hj => Holds.mono (hu j hj) (by norm_num) (by norm_num)))
  intro uh huh
  obtain ⟨uh, pdu⟩ := uh
  apply WP.spec_bind (mul_cache_spec P.VectorInst hP.vec hP.cache uh _ (fun j hj => Holds.congr (huh j hj)))
  intro uc huc
  obtain ⟨uc, pdc⟩ := uc
  apply WP.spec_bind (dot_and_inverse_ntt_spec P.VectorInst hP.vec hP.cache sh uh uc _ _
    (fun j hj => Holds.mono (hsh j hj) (by norm_num) (by norm_num)) (fun j hj => Holds.congr (huh j hj)) huc)
  intro t ht
  obtain ⟨t, pdt⟩ := t
  apply WP.spec_bind (sub_spec a t _ _ (Holds.congr ha) (Holds.congr ht) (fun p hp => by
    have h1 := ha p hp
    have h2 := ht p hp
    dsimp only at h1 h2
    constructor <;> omega))
  intro w hw
  apply WP.spec_mono (to_message_bits_spec w _ hw)
  intro m hm
  rw [hm]
  have hU : decompU c_1.val hc1 = decompU c.val (by omega) := by
    funext j
    unfold decompU
    split_ifs with hj
    · congr 3
      rw [hv1, hi3, hi1, hs]
      simp only [sub, List.drop_take, List.take_take]
      congr 1
      omega
    · rfl
  unfold decrypt
  simp only [hU]

/-! ## FIPS 203's `K-PKE.Decrypt` -/

theorem sub_getElem! (l : List U8) (off len i : ℕ) (hi : i < len) : (sub l off len)[i]! = l[off + i]! := by
  simp only [sub, List.getElem!_eq_getElem?_getD, List.getElem?_take, hi, ite_true, List.getElem?_drop]

theorem toVec_getElem (n : ℕ) (l : List U8) (h : l.length = n) (i : ℕ) (hi : i < n) :
    (toVec n l h)[i] = (l[i]!).bv := by
  simp only [toVec, bv, Vector.getElem_mk, List.getElem_toArray, List.getElem_map]
  rw [getElem!_pos l i (by omega)]

theorem slice_toVec {n : ℕ} (l : List U8) (h : l.length = n) (off len : ℕ) (h' : off + len ≤ n) :
    slice (toVec n l h) off len h' = toVec len (sub l off len) (sub_length _ _ _ (by omega)) := by
  apply Vector.ext
  intro i hi
  simp only [slice, Vector.getElem_ofFn, toVec_getElem, sub_getElem! _ _ _ _ hi]

theorem innerProductNTT_768 (v w : PolyVector q (k .ML_KEM_768)) :
    PolyVector.innerProductNTT v w = MultiplyNTTs v[0] w[0] + MultiplyNTTs v[1] w[1] + MultiplyNTTs v[2] w[2] := by
  unfold PolyVector.innerProductNTT
  simp [Id.run, Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size, k, List.range'_succ, Polynomial.zero_add]
  rfl

/-- `dk`'s three encoded polynomials as `K-PKE`'s decryption key. -/
def dkPke (dk : Enc) : 𝔹 1152 :=
  toVec 1152 (dk.val.flatMap (·.val)) (by rw [flat_length, dk.property]; rfl)

theorem sub_flat (dk : Enc) (j off len : ℕ) (hj : j < 3) (ho : off = 384 * j) (hl : len = 384) :
    sub (dk.val.flatMap (·.val)) off len = (dk.val[j]!).val := by
  subst ho hl
  have hl : (dk.val.flatMap (·.val)).length = 1152 := by rw [flat_length, dk.property]; rfl
  have hd : dk.val.length = 3 := dk.property
  apply List.ext_getElem
  · rw [sub_length _ _ _ (by omega), (dk.val[j]!).property]; rfl
  · intro p h1 h2
    have hp : p < 384 := by rw [sub_length _ _ _ (by omega)] at h1; exact h1
    rw [← getElem!_pos (sub _ _ _) p h1, ← getElem!_pos _ p h2, sub_getElem! _ _ _ _ hp]
    exact flat_getElem! dk.val j p (by omega) hp

theorem slice_cast {n n' : ℕ} (v : 𝔹 n) (h : n = n') (off len : ℕ) (h1 : off + len ≤ n') :
    slice (v.cast h) off len h1 = slice v off len (by omega) := by
  apply Vector.ext
  intro i hi
  simp [slice]

theorem sub_sub0 (l : List U8) (a off len : ℕ) (h : off + len ≤ a) : sub (sub l 0 a) off len = sub l off len := by
  simp only [sub, List.drop_zero, List.drop_take, List.take_take]
  congr 1
  omega

/-- `decrypt` is `K-PKE.Decrypt`'s `w`. -/
theorem decrypt_fips (dk : Enc) (c : CtBytes) :
    ByteEncode 1 (Polynomial.Compress 1 (decrypt dk c.val c.property)) =
      K_PKE.Decrypt .ML_KEM_768 (dkPke dk) (toVec 1088 c.val c.property) := by
  unfold K_PKE.Decrypt
  rw [show toVec 1088 c.val c.property =
    toVec (32 * (dᵤ .ML_KEM_768 * k .ML_KEM_768 + dᵥ .ML_KEM_768)) c.val c.property from rfl]
  simp only [innerProductNTT_768, PolyVector.NTT, PolyVector.Decompress, PolyVector.ByteDecode,
    Vector.getElem_map, Vector.getElem_ofFn, slice_cast, slice_toVec, dkPke]
  simp (disch := decide) only [sub_sub0]
  simp only [sub_flat dk 0 (32 * 12 * 0) (32 * 12) (by decide) rfl rfl,
    sub_flat dk 1 (32 * 12 * 1) (32 * 12) (by decide) rfl rfl, sub_flat dk 2 (32 * 12 * 2) (32 * 12) (by decide) rfl rfl]
  rfl

/-- `kpke_decrypt` is FIPS 203's `K-PKE.Decrypt` for ML-KEM-768. -/
theorem kpke_decrypt_fips {X : Type} (P : mid.mlkem.Params X Vec Mat EkBytes CtBytes DkBytes Cache Enc)
    (hP : Is768 P) (key : mid.mlkem.DecapKey X Vec Mat EkBytes CtBytes DkBytes Cache Enc) (c : CtBytes) :
    mid.mlkem.DecapKey.kpke_decrypt P key c ⦃ m =>
      toVec 32 m.val m.property = K_PKE.Decrypt .ML_KEM_768 (dkPke key.dk_pke) (toVec 1088 c.val c.property) ⦄ := by
  apply WP.spec_mono (kpke_decrypt_spec P hP key c)
  intro m hm
  rw [← decrypt_fips]
  exact hm

end MlKemPke

end rind.aarch64
