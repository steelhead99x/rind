import Rind.X86_64.MlKemCoding
import Rind.X86_64.Sha3
open Aeneas Aeneas.Std Result rind.spec Spec Spec.MLKEM rind.spec.mlkem

/-!
# ML-KEM's noise sampling

`sample_poly_cbd` writes FIPS 203's `SamplePolyCBD_2(PRF_2(σ, N))` into each
polynomial it fills, `N` counting up from its first, as K-PKE's key generation
and encryption sample their noise: `sample_poly_cbd_4x` hashes up to four
inputs at once through `shake256_batch_spec`, and `sample_cbd2_spec` turns
each output into its polynomial. η = 2 is all ML-KEM-768 and ML-KEM-1024
sample; ML-KEM-512's η₁ of 3 runs through another sponge, which this leaves
out. `admin/prove` writes aarch64's copy from this file by renaming the
target.
-/

namespace rind.x86_64

namespace MlKemCbd

open MlKemCoding

abbrev Poly := Std.Array I16 256#usize

/-- FIPS 203's `SamplePolyCBD_2(PRF_2(σ, N))`. -/
def cbd2 (sigma : Std.Array U8 32#usize) (N : ℕ) : Polynomial :=
  SamplePolyCBD (η := η₂) (PRF η₂ (toVec 32 sigma.val sigma.property) (N : Byte))

/-- SHAKE256's input for `PRF_2(σ, N)`: `σ ‖ N`. -/
abbrev prfInput (sigma : Std.Array U8 32#usize) (N : ℕ) : List Byte := bv sigma.val ++ [(N : Byte)]

theorem prfInput_length (sigma : Std.Array U8 32#usize) (N : ℕ) : (prfInput sigma N).length = 33 := by
  simp [prfInput, bv_length, sigma.property]

/-- SHAKE256 depends only on its input's bytes. -/
theorem shake256_congr {n n' : ℕ} (B : 𝔹 n) (C : 𝔹 n') (h : B.toList = C.toList) (d : ℕ) :
    Spec.SHA3.shake256 B d = Spec.SHA3.shake256 C d := by
  have hn : n = n' := by rw [← B.length_toList, ← C.length_toList, h]
  subst hn
  rw [Vector.toList_inj.mp h]

theorem shake256_toList_congr {n n' : ℕ} (B : 𝔹 n) (C : 𝔹 n') (h : B.toList = C.toList) (d d' : ℕ)
    (hd : d = d') : (Spec.SHA3.shake256 B d).toList = (Spec.SHA3.shake256 C d').toList := by
  subst hd
  rw [shake256_congr B C h]

theorem toVec_toList (n : ℕ) (l : List U8) (h : l.length = n) : (toVec n l h).toList = bv l := by
  simp [toVec]

/-- 128 bytes of SHAKE256 on `σ ‖ N` are `PRF_2(σ, N)`. -/
theorem prf_eq (sigma : Std.Array U8 32#usize) (N : ℕ) (out : List U8) (hl : out.length = 64 * η₂.val)
    (h : bv out = shake256 (prfInput sigma N) 128) :
    toVec (64 * η₂.val) out hl = PRF η₂ (toVec 32 sigma.val sigma.property) (N : Byte) := by
  apply Vector.toList_inj.mp
  rw [toVec_toList, h, shake256_eq]
  unfold PRF
  refine shake256_toList_congr _ _ ?_ _ _ rfl
  show bv sigma.val ++ [(N : Byte)] = _
  rw [show ∀ {m n : ℕ} (a : 𝔹 m) (b : 𝔹 n), Vector.append a b = a ++ b from fun _ _ => rfl,
    Vector.toList_append, toVec_toList]
  rfl

/-! ## `sample_poly_cbd_4x` -/

/-- `x` is SHAKE256's padded input for `PRF_2(σ, N)`, as `shake256_batch` takes it. -/
def PrfBlock (x : Std.Array U8 40#usize) (sigma : Std.Array U8 32#usize) (N : ℕ) : Prop :=
  bv x.val = prfInput sigma N ++ shakePad :: List.replicate 6 0

/-- The input `sample_poly_cbd_4x` builds in a zeroed block is `PRF_2`'s. -/
theorem prf_block (sigma : Std.Array U8 32#usize) (N : ℕ) (x : U8) (hx : x.val = N) :
    bv ((((List.replicate 40 0#u8).setSlice! 0 sigma.val).set 32 x).set 33 mid.sha3.SHAKE_PAD_BYTE) =
      prfInput sigma N ++ shakePad :: List.replicate 6 0 := by
  have hs : sigma.val.length = 32 := sigma.property
  have h1 : (List.replicate 40 0#u8).setSlice! 0 sigma.val = sigma.val ++ List.replicate 8 0#u8 := by
    simp only [List.setSlice!, List.take_zero, List.nil_append, List.length_replicate, Nat.sub_zero,
      Nat.zero_add, hs, List.drop_replicate]
    rw [List.take_of_length_le (by omega)]
    rfl
  have hxb : x.bv = (N : Byte) := by
    rw [← hx]
    apply BitVec.eq_of_toNat_eq
    simp [UScalar.bv_toNat]
  rw [h1, List.set_append_right _ _ (by omega), List.set_append_right _ _ (by simp), hs]
  simp only [bv, List.map_append, prfInput, List.append_assoc, shake_pad_byte_eq]
  simp [List.replicate_succ, hxb]
  rfl

/-- The input loop: input `t` is `σ ‖ n + t`, padded, for each `t` below `count`. -/
theorem cbd_inputs_spec (sigma : Std.Array U8 32#usize) (n : U8) (count : Usize) (hc : count.val ≤ 4)
    (hn : n.val + count.val ≤ 256) (iter : core.ops.range.Range Usize) (hs : iter.start.val = 0)
    (he : iter.end.val = count.val) :
    mid.mlkem.sample_poly_cbd_4x_loop0 iter sigma n
      (Std.Array.repeat 4#usize (Std.Array.repeat 40#usize 0#u8)) ⦃ r =>
      ∀ j < count.val, PrfBlock (r.val[j]!) sigma (n.val + j) ⦄ := by
  unfold mid.mlkem.sample_poly_cbd_4x_loop0
  apply WP.spec_mono (range_loop count.val (fun i (s : Std.Array (Std.Array U8 40#usize) 4#usize) =>
    ∀ j < 4, (j < i → PrfBlock (s.val[j]!) sigma (n.val + j)) ∧
      (i ≤ j → (s.val[j]!).val = List.replicate 40 0#u8)) _ ?_ iter _ he (by omega) ?_)
  · intro r hr j hj
    exact (hr j (by omega)).1 hj
  · intro it s he hs hinv
    simp only
    unfold mid.mlkem.sample_poly_cbd_4x_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have ht4 : it.start.val < 4 := by omega
      step as ⟨a, back, ha, hback⟩
      step as ⟨s0, back1, hs0, hs0l, hback1⟩
      step as ⟨s1, hs1⟩
      step with core.slice.Slice.copy_from_slice.step_spec _ s0 s1 (by
          rw [hs0l]; simp [Slice.length, hs1, sigma.property]) as ⟨s2, hs2⟩
      step as ⟨i, hi⟩
      have hiv : i.val = it.start.val := by
        rw [hi, UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by simp; omega)
      step as ⟨i1, hi1⟩
      step as ⟨a2, back2, ha2, hback2⟩
      step as ⟨a3, ha3⟩
      step as ⟨a4, back3, ha4, hback3⟩
      step as ⟨a5, ha5⟩
      refine ⟨by rw [he1]; exact he, hst, by omega, fun j hj => ?_⟩
      subst hback hback2 hback3
      have hz : a.val = List.replicate 40 0#u8 := by
        rw [ha, ← getElem!_pos]
        exact (hinv _ ht4).2 le_rfl
      have hfin : a5.val = (((List.replicate 40 0#u8).setSlice! 0 sigma.val).set 32 i1).set 33
          mid.sha3.SHAKE_PAD_BYTE := by
        rw [ha5, Std.Array.set_val_eq, ha4, ← getElem!_pos, array_set_getElem! _ _ _ _ (by simp; omega),
          ite_eq_left rfl, ha3, Std.Array.set_val_eq, ha2, ← getElem!_pos,
          array_set_getElem! _ _ _ _ (by simp; omega), ite_eq_left rfl, hback1, hs2, hs1, hz, Std.Array.val_to_slice]
        rfl
      rw [array_set_getElem! _ _ _ _ (by simp; omega), array_set_getElem! _ _ _ _ (by simp; omega),
        array_set_getElem! _ _ _ _ (by simp; omega)]
      by_cases hjt : j = it.start.val
      · simp only [hjt, ite_true]
        refine ⟨fun _ => ?_, fun h => by omega⟩
        unfold PrfBlock
        rw [hfin]
        exact prf_block sigma _ i1 (by rw [hi1, hiv])
      · simp only [hjt, ite_false]
        obtain ⟨h1, h2⟩ := hinv j hj
        exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
    · obtain ⟨rfl, hst⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = count.val := by omega
      rw [this] at hinv
      exact hinv
  · intro j hj
    rw [hs]
    refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
    rw [Std.Array.repeat_val, List.getElem!_replicate _ (by scalar_tac), Std.Array.repeat_val]
    rfl

/-- `try_from` of a mutable slice as long as the array. -/
theorem try_from_mut_spec {T : Type} (N : Usize) (s : Slice T) (h : s.length = N.val) :
    core.array.TryFromMutArraySlice.try_from N s ⦃
      (r : core.result.Result (Std.Array T N) core.array.TryFromSliceError)
      (back : core.result.Result (Std.Array T N) core.array.TryFromSliceError → Slice T) =>
      r = .Ok (Std.Array.from s.val h) ∧ ∀ a : Std.Array T N, (back (.Ok a)).val = a.val ⦄ := by
  have hc : s.len = N := by scalar_tac
  unfold core.array.TryFromMutArraySlice.try_from
  rw [dite_eq_left hc]
  simp only [WP.spec_ok, WP.uncurry'_pair]
  refine ⟨trivial, fun a => ?_⟩
  rw [ite_eq_left (by have := a.property; simp only [Std.Array.length, Slice.length] at *; omega)]
  exact Slice.from_val _ _

/-- `try_from` of a shared slice as long as the array. -/
theorem try_from_eq {T : Type} (N : Usize) (s : Slice T) (h : s.length = N.val) :
    core.array.TryFromSharedArraySlice.try_from N s = ok (.Ok (Std.Array.from s.val h)) := by
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dite_eq_left (by scalar_tac)]

theorem unwrap_mut_spec {T E : Type} (d : core.fmt.Debug E) (x : T) :
    core.result.Result.unwrap.mut d (.Ok x : core.result.Result T E) ⦃ (y : T)
      (back : T → core.result.Result T E) => y = x ∧ ∀ z, back z = .Ok z ⦄ := by
  simp [core.result.Result.unwrap.mut, WP.spec_ok]

/-- `shake256_batch` of the first `P` inputs, into the first `P` outputs, as
`sample_poly_cbd_4x` calls it for fewer than four polynomials. -/
theorem batch_spec (h : RunsSha3) (P : Usize) (hP : P.val ≤ 4)
    (inputs : Std.Array (Std.Array U8 40#usize) 4#usize) (samples : Std.Array (Std.Array U8 128#usize) 4#usize)
    (sigma : Std.Array U8 32#usize) (n : ℕ) (hin : ∀ j < P.val, PrfBlock (inputs.val[j]!) sigma (n + j)) :
    (do
      let s ← core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Std.Array U8 40#usize))) inputs { «end» := P }
      let r ← core.array.TryFromSharedArraySlice.try_from P s
      let a3 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let (s1, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Std.Array U8 128#usize))) samples { «end» := P }
      let (r1, try_from_back) ← core.array.TryFromMutArraySlice.try_from P s1
      let (a4, unwrap_back) ← core.result.Result.unwrap.mut core.fmt.DebugTryFromSliceError r1
      let a5 ← mid.sha3.shake256_batch a3 a4
      let r2 := unwrap_back a5
      let s2 := try_from_back r2
      ok (index_mut_back s2)) ⦃ r =>
      ∀ j < P.val, bv (r.val[j]!).val = shake256 (prfInput sigma (n + j)) 128 ⦄ := by
  simp only [Array.index_SliceIndexRangeToUsizeSlice]
  step as ⟨s, hsv, hsl⟩
  rw [try_from_eq P s hsl]
  simp only [core.result.Result.unwrap, bind_ok]
  step as ⟨s1, back, hs1v, hs1l, hback⟩
  step with try_from_mut_spec P s1 hs1l as ⟨r1, tback, hr1, htback⟩
  subst hr1
  step with unwrap_mut_spec core.fmt.DebugTryFromSliceError _ as ⟨a4, uback, ha4, huback⟩
  subst ha4
  have hin' : Shake256Inputs (Std.Array.from s.val hsl) (fun j => prfInput sigma (n + j)) := by
    intro j hj
    refine ⟨prfInput_length _ _, ?_⟩
    have := inputs.property
    rw [Std.Array.from_val, hsv, Std.Array.val_to_slice, List.getElem!_slice _ _ _ _ ⟨by scalar_tac, by omega⟩, Nat.zero_add]
    exact hin j hj
  refine WP.spec_bind (shake256_batch_spec h _ _ hin' _) ?_
  intro a5 ha5
  apply (WP.spec_ok _).2
  intro j hj
  have := samples.property
  rw [hback, huback, htback a5, List.getElem!_setSlice!_middle _ _ _ _
    ⟨Nat.zero_le _, by rw [a5.property]; omega, by scalar_tac⟩, Nat.sub_zero]
  exact ha5 j hj

/-- The sampling loop: polynomial `t` is `SamplePolyCBD_2` of output `t`. -/
theorem cbd_samples_spec (sigma : Std.Array U8 32#usize) (n : ℕ) (count : Usize) (hc : count.val ≤ 4)
    (samples : Std.Array (Std.Array U8 128#usize) 4#usize)
    (hs : ∀ j < count.val, bv (samples.val[j]!).val = shake256 (prfInput sigma (n + j)) 128)
    (iter : core.ops.range.Range Usize) (hst : iter.start.val = 0) (he : iter.end.val = count.val)
    (polys : Std.Array Poly 4#usize) :
    mid.mlkem.sample_poly_cbd_4x_loop1 iter polys samples ⦃ r =>
      ∀ t < count.val, Holds (-2) 2 256 (r.val[t]!).val (cbd2 sigma (n + t)) ⦄ := by
  unfold mid.mlkem.sample_poly_cbd_4x_loop1
  apply WP.spec_mono (range_loop count.val (fun i (s : Std.Array Poly 4#usize) =>
    ∀ t < i, Holds (-2) 2 256 (s.val[t]!).val (cbd2 sigma (n + t))) _ ?_ iter _ he (by omega)
    (fun t ht => absurd ht (by omega)))
  · intro r hr
    exact hr
  · intro it s he hs' hinv
    simp only
    unfold mid.mlkem.sample_poly_cbd_4x_loop1.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst'⟩ := ho
      simp only
      step as ⟨a, ha⟩
      step as ⟨a1, back, ha1, hback⟩
      step with sample_cbd2_spec (η := η₂) rfl a a1 as ⟨a2, ha2⟩
      refine ⟨by rw [he1]; exact he, hst', by omega, fun t ht => ?_⟩
      subst hback
      rw [array_set_getElem! _ _ _ _ (by simp; omega)]
      by_cases htt : t = it.start.val
      · subst htt
        simp only [ite_true]
        have hp := prf_eq sigma (n + it.start.val) a.val (by rw [a.property]; rfl)
          (by rw [ha, ← getElem!_pos]; exact hs _ (by omega))
        rw [hp] at ha2
        exact ha2
      · simp only [htt, ite_false]
        exact hinv t (by omega)
    · obtain ⟨rfl, hst'⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = count.val := by omega
      rw [this] at hinv
      exact hinv

/-- `sample_poly_cbd_4x` with η = 2: polynomial `t` is `SamplePolyCBD_2(PRF_2(σ, n + t))`
for each `t` below `count`, of one to four. -/
theorem sample_poly_cbd_4x_spec (h : RunsSha3) (sigma : Std.Array U8 32#usize) (n : U8) (count : Usize)
    (hc : 1 ≤ count.val ∧ count.val ≤ 4) (hn : n.val + count.val ≤ 256) :
    mid.mlkem.sample_poly_cbd_4x 2#usize sigma n count ⦃ polys =>
      ∀ t < count.val, Holds (-2) 2 256 (polys.val[t]!).val (cbd2 sigma (n.val + t)) ⦄ := by
  unfold mid.mlkem.sample_poly_cbd_4x
  simp only [show (2#usize : Usize).val = 2 from rfl]
  step with cbd_inputs_spec sigma n count hc.2 hn { start := 0#usize, «end» := count } rfl rfl
    as ⟨inputs, hin⟩
  apply WP.spec_bind (Pₘ := fun samples : Std.Array (Std.Array U8 128#usize) 4#usize =>
    ∀ j < count.val, bv (samples.val[j]!).val = shake256 (prfInput sigma (n.val + j)) 128)
  · obtain hcv | hcv | hcv | hcv : count.val = 1 ∨ count.val = 2 ∨ count.val = 3 ∨ count.val = 4 := by omega
    · simp only [hcv]
      apply WP.spec_mono (batch_spec h 1#usize (by decide) inputs _ sigma n.val
        (fun j hj => hin j (by simp at hj; omega)))
      intro r hr j hj
      exact hr j (by simp; omega)
    · simp only [hcv]
      apply WP.spec_mono (batch_spec h 2#usize (by decide) inputs _ sigma n.val
        (fun j hj => hin j (by simp at hj; omega)))
      intro r hr j hj
      exact hr j (by simp; omega)
    · simp only [hcv]
      apply WP.spec_mono (batch_spec h 3#usize (by decide) inputs _ sigma n.val
        (fun j hj => hin j (by simp at hj; omega)))
      intro r hr j hj
      exact hr j (by simp; omega)
    · simp only [hcv]
      apply WP.spec_mono (shake256_batch_spec h inputs (fun j => prfInput sigma (n.val + j))
        (fun j hj => ⟨prfInput_length _ _, hin j (by simp at hj; omega)⟩) _)
      intro r hr j hj
      exact hr j (by simp; omega)
  · intro samples hs
    exact cbd_samples_spec sigma n.val count hc.2 samples hs _ rfl rfl _

/-! ## `sample_poly_cbd` -/

/-- Polynomial `p` of `a` then `b`. -/
def get2 (a b : Slice Poly) (p : ℕ) : Poly := if p < a.length then a.val[p]! else b.val[p - a.length]!

/-- The copying loop: polynomial `done + t` of `a` then `b` is `polys`' `t`th. -/
theorem cbd_copy_spec (sigma : Std.Array U8 32#usize) (first : ℕ) (done count : Usize)
    (polys : Std.Array Poly 4#usize) (a b : Slice Poly) (hc : count.val ≤ 4)
    (hd : done.val + count.val ≤ a.length + b.length) (hab : a.length + b.length ≤ 256)
    (hp : ∀ t < count.val, Holds (-2) 2 256 (polys.val[t]!).val (cbd2 sigma (first + done.val + t)))
    (hpre : ∀ p < done.val, Holds (-2) 2 256 (get2 a b p).val (cbd2 sigma (first + p)))
    (iter : core.ops.range.Range Usize) (hst : iter.start.val = 0) (he : iter.end.val = count.val) :
    mid.mlkem.sample_poly_cbd_loop0_loop0 iter a b done polys ⦃ r =>
      r.1.length = a.length ∧ r.2.length = b.length ∧
      ∀ p < done.val + count.val, Holds (-2) 2 256 (get2 r.1 r.2 p).val (cbd2 sigma (first + p)) ⦄ := by
  unfold mid.mlkem.sample_poly_cbd_loop0_loop0
  apply WP.spec_mono (range_loop count.val (fun i (s : Slice Poly × Slice Poly) =>
    s.1.length = a.length ∧ s.2.length = b.length ∧
      ∀ p < done.val + i, Holds (-2) 2 256 (get2 s.1 s.2 p).val (cbd2 sigma (first + p))) _ ?_ iter (a, b)
    he (by omega) ⟨rfl, rfl, by rw [hst]; exact hpre⟩)
  · intro r hr
    exact hr
  · rintro it ⟨sa, sb⟩ he hs' ⟨hla, hlb, hinv⟩
    simp only at hla hlb hinv ⊢
    unfold mid.mlkem.sample_poly_cbd_loop0_loop0.body
    step as ⟨o', it1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst'⟩ := ho
      simp only
      have hmax : done.val + it.start.val ≤ Usize.max := by scalar_tac
      step as ⟨poly, hpoly⟩
      have hpt : Holds (-2) 2 256 (polys.val[it.start.val]!).val (cbd2 sigma (first + poly.val)) := by
        rw [hpoly, ← Nat.add_assoc]; exact hp _ (by omega)
      split
      · rename_i hlt'
        step as ⟨x, hx⟩
        step as ⟨s, hs⟩
        refine ⟨by rw [he1]; exact he, hst', by omega, ?_, hlb, fun p hp' => ?_⟩
        · rw [hs, Slice.set_length]; exact hla
        · have hlt'' : poly.val < sa.length := by scalar_tac
          unfold get2
          rw [hs, Slice.set_length]
          unfold get2 at hinv
          by_cases hpp : p = poly.val
          · subst hpp
            rw [ite_eq_left hlt'', Slice.set_val_eq, getElem!_set_self _ _ _ (by exact hlt''), hx,
              ← getElem!_pos]
            exact hpt
          · split_ifs with h1
            · rw [Slice.set_val_eq, getElem!_set_ne _ _ _ _ (Ne.symm hpp)]
              have := hinv p (by omega)
              rwa [ite_eq_left h1] at this
            · have := hinv p (by omega)
              rwa [ite_eq_right h1] at this
      · rename_i hge
        step as ⟨x, hx⟩
        step as ⟨i2, hi2⟩
        step as ⟨s, hs⟩
        refine ⟨by rw [he1]; exact he, hst', by omega, hla, ?_, fun p hp' => ?_⟩
        · rw [hs, Slice.set_length]; exact hlb
        · have hge' : sa.length ≤ poly.val := by scalar_tac
          have hsal : (Slice.len sa).val = sa.length := by rw [Slice.len_val]
          unfold get2
          unfold get2 at hinv
          by_cases hpp : p = poly.val
          · subst hpp
            rw [ite_eq_right (by omega), hs, Slice.set_val_eq, hi2, hsal, getElem!_set_self _ _ _ (by
              have : sb.val.length = sb.length := rfl; omega), hx, ← getElem!_pos]
            exact hpt
          · split_ifs with h1
            · have := hinv p (by omega)
              rwa [ite_eq_left h1] at this
            · rw [hs, Slice.set_val_eq, getElem!_set_ne _ _ _ _ (by rw [hi2, hsal]; omega)]
              have := hinv p (by omega)
              rwa [ite_eq_right h1] at this
    · obtain ⟨rfl, hst'⟩ := ho
      apply (WP.spec_ok _).2
      have : it.start.val = count.val := by omega
      rw [this] at hinv
      exact ⟨hla, hlb, hinv⟩

/-- `sample_poly_cbd` with η = 2: polynomial `p` of `a` then `b` is
`SamplePolyCBD_2(PRF_2(σ, first + p))`. -/
theorem sample_poly_cbd_spec (h : RunsSha3) (sigma : Std.Array U8 32#usize) (first : U8) (a b : Slice Poly)
    (hf : first.val + a.length + b.length ≤ 256) :
    mid.mlkem.sample_poly_cbd 2#usize sigma first a b ⦃ r =>
      r.1.length = a.length ∧ r.2.length = b.length ∧
      ∀ p < a.length + b.length, Holds (-2) 2 256 (get2 r.1 r.2 p).val (cbd2 sigma (first.val + p)) ⦄ := by
  unfold mid.mlkem.sample_poly_cbd
  step as ⟨total, htotal⟩
  have ht : total.val = a.length + b.length := by scalar_tac
  unfold mid.mlkem.sample_poly_cbd_loop0
  apply loop.spec_decr_nat (fun x => total.val - x.2.2.val)
    (fun x => x.1.length = a.length ∧ x.2.1.length = b.length ∧ x.2.2.val ≤ total.val ∧
      ∀ p < x.2.2.val, Holds (-2) 2 256 (get2 x.1 x.2.1 p).val (cbd2 sigma (first.val + p)))
  · rintro ⟨sa, sb, d⟩ ⟨hla, hlb, hd, hinv⟩
    simp only at hla hlb hd hinv ⊢
    unfold mid.mlkem.sample_poly_cbd_loop0.body
    split
    · rename_i hlt
      have hlt' : d.val < total.val := by scalar_tac
      step as ⟨i, hi⟩
      have hcount : ∃ c : Usize, (if i < 4#usize then ok i else ok 4#usize : Result Usize) = ok c ∧
          c.val = min (total.val - d.val) 4 := by
        split_ifs with h4
        · exact ⟨i, rfl, by rw [Nat.min_def]; split_ifs <;> scalar_tac⟩
        · exact ⟨4#usize, rfl, by rw [Nat.min_def]; split_ifs <;> scalar_tac⟩
      obtain ⟨count, hc1, hcv⟩ := hcount
      rw [hc1, bind_ok]
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = d.val := by
        rw [hi1, UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by simp; omega)
      step as ⟨i2, hi2⟩
      step with sample_poly_cbd_4x_spec h sigma i2 count ⟨by omega, by omega⟩ (by omega) as ⟨polys, hpolys⟩
      step with cbd_copy_spec sigma first.val d count polys sa sb (by omega) (by omega) (by omega)
          (fun t ht => by rw [← hi1v, ← hi2]; exact hpolys t ht)
          hinv { start := 0#usize, «end» := count } rfl rfl as ⟨r1, r2, hl1, hl2, hr⟩
      step as ⟨d2, hd2⟩
      refine ⟨by rw [hl1, hla], by rw [hl2, hlb], by omega, fun p hp => hr p (by omega), by omega⟩
    · rename_i hge
      simp only [WP.spec_ok]
      have : total.val ≤ d.val := by scalar_tac
      refine ⟨hla, hlb, fun p hp => hinv p (by omega)⟩
  · exact ⟨rfl, rfl, by simp, fun p hp => absurd hp (by simp)⟩

end MlKemCbd

end rind.x86_64
