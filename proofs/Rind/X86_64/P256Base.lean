import Rind.X86_64.P256Agree
import Rind.X86_64.PointSelect
import Rind.X86_64.P256Table
import Rind.P256Booth
import Rind.P256Multiples
open Aeneas Aeneas.Std Result rind.spec rind.spec.booth256

/-!
# x86_64's P-256 generator multiplication

`base_multiply_spec` proves that x86_64's `AffineMontPoint::base_multiply`,
rind's port of aws-lc's `ecp_nistz256_point_mul_base`, computes k·G for a
scalar k below n, with the statement aarch64's s2n-bignum one has, and
`jac_base_multiply_spec` that `JacobianMontPoint::base_multiply`, before its
affine conversion, represents k·G.

The driver Booth-recodes k into 37 signed 7-bit digits (`booth_w7_spec`,
whose arithmetic `Rind.P256Booth` proves), selects each digit's multiple of
2⁷ʷ·G from row w of the generator table, which `Rind.X86_64.P256Table` checks,
and adds it with aws-lc's mixed addition, which never doubles (`booth_ne`).
The select is rind's Rust, which `Rind.X86_64.PointSelect` proves; the addition
is opaque, and `S2nBignum.lean`'s placeholder `p256_point_add_affine_spec`
states what it computes until its HOL Light proof lands.
-/

set_option exponentiation.threshold 400

namespace rind.x86_64

namespace P256Base

open P256

/-! ## Limbs -/

theorem wordsNat_inj : ∀ (a b : List U64), a.length = b.length → wordsNat a = wordsNat b → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [wordsNat, List.map_cons, Nat.ofDigits_cons] at h
    have hx := x.hBounds
    have hy := y.hBounds
    simp only [UScalarTy.numBits] at hx hy
    have e : x.val = y.val := by omega
    have e' : wordsNat xs = wordsNat ys := by simp only [wordsNat]; omega
    rw [UScalar.eq_of_val_eq e, wordsNat_inj xs ys (by simpa using hl) e']

theorem wordsNat_replicate (n : Nat) : wordsNat (List.replicate n 0#u64) = 0 := by
  induction n with
  | zero => simp [wordsNat, Nat.ofDigits]
  | succ n ih =>
    simp only [wordsNat, List.replicate_succ, List.map_cons, Nat.ofDigits_cons] at ih ⊢
    rw [ih]; rfl

theorem pairNat_take8 (l : List U64) : pairNat (l.take 8) = pairNat l := by
  simp [pairNat, List.take_take, List.drop_take]

/-! ## Selects and negation -/

theorem runsSelect_of_runs (h : Runs) : RunsSelect := h.2.2.2

/-- `bignum_aff_point_select_p256` on one 64-entry row of the table: entry
`index`, counting from 1, or zeros for any other index. -/
@[step]
theorem select_row_spec (hc : RunsSelect) (z : Std.Array U64 8#usize) (table : Slice U64) (index : U8)
    (ht : table.length = 512) :
    low.x86_64.bignum_point_select.bignum_aff_point_select_p256 z table index ⦃ r =>
      r.val = if 1 ≤ index.val ∧ index.val ≤ 64 then (table.val.drop (8 * (index.val - 1))).take 8
        else List.replicate 8 0#u64 ⦄ := by
  apply WP.spec_mono (bignum_aff_point_select_p256_spec hc z table index (by rw [ht]; norm_num))
  intro r hr
  have hl : table.val.length = 512 := ht
  rw [hr, tableRow, hl]

/-- What `bignum_aff_point_select_p256` selects from a 64-entry row: entry
`d`, counting from 1, or zeros for any other `d`. -/
def sel (row : Std.Array U64 512#usize) (d : Nat) : List U64 :=
  if 1 ≤ d ∧ d ≤ 64 then (row.val.drop (8 * (d - 1))).take 8 else List.replicate 8 0#u64

theorem sel_zero (row : Std.Array U64 512#usize) : pairNat (sel row 0) = (0, 0) := by
  simp [sel, pairNat, wordsNat, Nat.ofDigits]

@[step]
theorem fe_negate_spec (a : mid.p256.FieldElement) (ha : feNat a ≤ p256) :
    mid.p256.FieldElement.negate_mod_p a ⦃ r => feNat r = (p256 - feNat a) % p256 ⦄ := by
  unfold mid.p256.FieldElement.negate_mod_p mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

theorem from_u8_val (v : U8) : (core.convert.num.FromU64U8.from v).val = v.val := by
  simp only [core.convert.num.FromU64U8.from]
  show (BitVec.setWidth 64 v.bv).toNat = v.bv.toNat
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_trans v.bv.isLt (by norm_num))

/-- `select_w7` selects entry `digit` of `row`, and negates its y mod p when
`negate` is nonzero. -/
theorem select_w7_spec (hc : RunsSelect) (pt : mid.p256.AffineMontPoint) (row : Std.Array U64 512#usize) (digit negate : U8)
    (hy : (pairNat (sel row digit.val)).2 ≤ p256) :
    mid.p256.AffineMontPoint.select_w7 pt row digit negate ⦃ r =>
      pairNat r.xy.val = ((pairNat (sel row digit.val)).1,
        if negate.val = 0 then (pairNat (sel row digit.val)).2
        else (p256 - (pairNat (sel row digit.val)).2) % p256) ⦄ := by
  unfold mid.p256.AffineMontPoint.select_w7
  simp only [lift, bind_ok]
  step with select_row_spec hc pt.xy row.to_slice digit (by simp) as ⟨a, ha⟩
  have ha' : a.val = sel row digit.val := by rw [ha]; simp [sel]
  have hl : a.val.length = 8 := a.property
  have hy' : wordsNat (a.val.drop 4) ≤ p256 := by rw [← pairNat_drop _ hl, ha']; exact hy
  have hY : mid.p256.AffineMontPoint.Y = { start := 4#usize, «end» := 8#usize } := by
    simp [mid.p256.AffineMontPoint.Y]
  step*
  · have hn := from_u8_val negate
    have hsl : s4.val.length = 4 := by
      have : s4.length = 4 := by rw [s4_post, s1_post1, hY]; rfl
      simpa [Slice.length] using this
    have hv : (index_mut_back s4).val = a.val.take 4 ++ s4.val := by
      rw [s1_post2, hY]
      simp only
      generalize a.val = l at hl ⊢
      match l, hl with
      | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
        generalize s4.val = q at hsl ⊢
        match q, hsl with
        | [b0, b1, b2, b3], _ => simp [List.setSlice!]
    rw [hv, pairNat_append _ _ (by simp [hl]) hsl, s4_post1, hn]
    have h1 : wordsNat (a.val.take 4) = (pairNat (sel row digit.val)).1 := by rw [← ha']; rfl
    have h2 : wordsNat (a.val.drop 4) = (pairNat (sel row digit.val)).2 := by rw [← ha', pairNat_drop _ hl]
    simp only [Array.val_to_slice]
    rw [h1]
    by_cases h0 : negate.val = 0
    · simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [show wordsNat y.val = wordsNat (a.val.drop 4) by rw [y_post], h2]
    · simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [show wordsNat fe.val = feNat fe from rfl, fe_post,
        show feNat y = wordsNat (a.val.drop 4) by simp [feNat, y_post], h2]

/-! ## Booth recoding -/

theorem bv_window_hi (a b : BitVec 64) (s : Nat) (hs : s < 64) :
    ((a >>> s ||| b <<< (64 - s)) &&& 255#64).toNat = (a.toNat + 2 ^ 64 * b.toNat) / 2 ^ s % 256 := by
  have h : (a >>> s ||| b <<< (64 - s)) &&& 255#64 = ((b ++ a) >>> s).setWidth 64 &&& 255#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h255 : (255#64).getLsbD i = decide (i < 8) := by
      rw [show (255#64) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
      simp [hi]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append, h255]
    by_cases h8 : i < 8
    · simp only [h8, decide_true, Bool.and_true, hi]
      by_cases ht : i < 64 - s
      · have : s + i < 64 := by omega
        simp [ht, this]
      · simp only [ht, show ¬ s + i < 64 by omega, decide_false, Bool.not_false, Bool.true_and]
        simp [BitVec.getLsbD_of_ge a (s + i) (by omega), show i - (64 - s) = s + i - 64 by omega]
    · simp [h8]
  rw [h, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 8 ∣ 2 ^ 64)]
  ring_nf

theorem bv_window_lo (a : BitVec 64) (s : Nat) :
    ((a >>> s) &&& 255#64).toNat = a.toNat / 2 ^ s % 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem wordsNat_chunk (l : List U64) (hl : l.length = 4) (i : Nat) (hi : i < 4) :
    wordsNat l / 2 ^ (64 * i) % 2 ^ 128 =
      (l[i]!).val + 2 ^ 64 * (if i + 1 < 4 then (l[i + 1]!).val else 0) := by
  match l, hl with
  | [a0, a1, a2, a3], _ =>
    have h0 := a0.hBounds; have h1 := a1.hBounds; have h2 := a2.hBounds; have h3 := a3.hBounds
    simp only [UScalarTy.numBits] at h0 h1 h2 h3
    simp only [wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil]
    interval_cases i <;> simp <;> omega

theorem window_bits (k w A B : Nat) (hAB : k / 2 ^ (64 * ((7 * w - 1) / 64)) % 2 ^ 128 = A + 2 ^ 64 * B) :
    k / 2 ^ (7 * w - 1) % 256 = (A + 2 ^ 64 * B) / 2 ^ ((7 * w - 1) % 64) % 256 := by
  set bit := 7 * w - 1
  have hs : bit % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : 2 ^ bit = 2 ^ (64 * (bit / 64)) * 2 ^ (bit % 64) := by
    rw [← pow_add, Nat.div_add_mod]
  have hd : 2 ^ (bit % 64) * 256 ∣ 2 ^ 128 := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [hb, ← Nat.div_div_eq_div_mul, ← Nat.mod_mul_right_div_self, ← Nat.mod_mod_of_dvd _ hd, hAB,
    Nat.mod_mul_right_div_self]

theorem window_lo (A B s : Nat) (hs : s ≤ 56) : (A + 2 ^ 64 * B) / 2 ^ s % 256 = A / 2 ^ s % 256 := by
  have hd : 2 ^ s * 256 ∣ 2 ^ 64 := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self A, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd B), add_zero, Nat.mod_mod]

/-- `booth_recode_w7`'s digit, on bit vectors. -/
def recodeD (x : BitVec 8) : BitVec 8 :=
  let sign := ~~~((x >>> 7) - 1)
  let d := ((1#16 <<< 8) - x.setWidth 16 - 1).setWidth 8
  let d1 := (d &&& sign) ||| (x &&& ~~~sign)
  (d1 >>> 1) + (d1 &&& 1)

/-- `booth_recode_w7`'s sign, on bit vectors. -/
def recodeS (x : BitVec 8) : BitVec 8 := ~~~((x >>> 7) - 1) &&& 1

/-- `booth_recode_w7` recodes every byte, checked byte by byte. -/
theorem recode_ok : ∀ x : BitVec 8,
    (recodeD x).toNat = boothD x.toNat ∧ (recodeS x).toNat = boothS x.toNat := by
  decide

theorem booth_recode_w7_spec (v : U8) :
    mid.p256.booth_recode_w7 v ⦃ d s => d.val = boothD v.val ∧ s.val = boothS v.val ⦄ := by
  unfold mid.p256.booth_recode_w7
  step*
  have hd : d2.bv = recodeD v.bv := by
    simp [d2_post, i9_post1, i10_post1, d1_post1, i6_post1, i8_post1, i7_post, d_post, i5_post, i4_post,
      i3_post, i2_post1, sign_post, i1_post, i_post1, recodeD, UScalar.cast_bv_eq]
  have hs : i11.bv = recodeS v.bv := by
    simp [i11_post1, sign_post, i1_post, i_post1, recodeS]
  have h := recode_ok v.bv
  simp only [UScalar.val, hd, hs]
  exact h

/-- The first `n` of `windows` hold `k`'s Booth digits and signs. -/
def WindowsOk (k : Nat) (windows : Std.Array (U8 × U8) 37#usize) (n : Nat) : Prop :=
  ∀ i < n, ((windows.val[i]!).1).val = boothD (window k i) ∧ ((windows.val[i]!).2).val = boothS (window k i)

theorem windowsOk_update (k : Nat) (windows : Std.Array (U8 × U8) 37#usize) (n : Nat) (hn : n < 37)
    (h : WindowsOk k windows n) (p : U8 × U8) (hp1 : p.1.val = boothD (window k n))
    (hp2 : p.2.val = boothS (window k n)) (idx : Usize) (hidx : idx.val = n) (w : Std.Array (U8 × U8) 37#usize)
    (hw : w = windows.set idx p) :
    WindowsOk k w (n + 1) := by
  have hl : windows.val.length = 37 := windows.property
  intro i hi
  rw [hw, Std.Array.set_val_eq, hidx]
  by_cases hin : i = n
  · subst hin
    simp_lists [hp1, hp2]
  · have h' := h i (by omega)
    simp_lists
    rwa [getElem!_pos _ _ (by omega)] at h'

theorem booth_w7_loop_spec (a : Std.Array U64 4#usize) (iter : core.ops.range.Range Usize)
    (windows : Std.Array (U8 × U8) 37#usize) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 37)
    (he : iter.end.val = 37) (hw : WindowsOk (wordsNat a.val) windows iter.start.val) :
    mid.p256.Scalar.booth_w7_loop iter a windows ⦃ r => WindowsOk (wordsNat a.val) r 37 ⦄ := by
  unfold mid.p256.Scalar.booth_w7_loop
  apply loop.spec_decr_nat (fun x => 37 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 37 ∧ x.1.end.val = 37 ∧
      WindowsOk (wordsNat a.val) x.2 x.1.start.val)
  · rintro ⟨it, ws⟩ ⟨hs1, hs, he, hw⟩
    simp only at hs1 hs he hw ⊢
    unfold mid.p256.Scalar.booth_w7_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have he1' : iter1.end.val = it.end.val := by rw [he1]
      step as ⟨i, hi⟩
      step as ⟨bit, hbit, hbit1⟩
      step as ⟨word, hword⟩
      step as ⟨shift, hshift⟩
      step as ⟨i1, hi1⟩
      step as ⟨value, hvalue0, hvalue⟩
      have hl : a.val.length = 4 := a.property
      have hwd : word.val < 4 := by omega
      have hchunk := wordsNat_chunk a.val hl word.val hwd
      have hwv : word.val = (7 * it.start.val - 1) / 64 := by omega
      have hsv : shift.val = (7 * it.start.val - 1) % 64 := by omega
      have hbits := window_bits (wordsNat a.val) it.start.val _ _ (by rw [← hwv]; exact hchunk)
      have hwin : window (wordsNat a.val) it.start.val = wordsNat a.val / 2 ^ (7 * it.start.val - 1) % 256 := by
        unfold window; simp [show it.start.val ≠ 0 by omega]
      have hA : i1 = a.val[word.val]! := by rw [hi1]; exact (getElem!_pos _ _ (by omega)).symm
      apply WP.spec_bind (Pₘ := fun x : core.ops.range.Range Usize × U64 =>
        x.1 = iter1 ∧ (x.2 &&& 255#u64).val = window (wordsNat a.val) it.start.val)
      · rw [hwin, hbits, ← hsv, ← hA]
        split
        · rename_i h56
          have h56' : 56 < shift.val := by scalar_tac
          split
          · rename_i h3
            have h3' : word.val < 3 := by scalar_tac
            step as ⟨w1, hw1⟩
            step as ⟨b1, hb1⟩
            step as ⟨t, ht, ht1⟩
            step as ⟨y, hy, hy1⟩
            simp only [show word.val + 1 < 4 by omega, ↓reduceIte]
            have hb : b1 = a.val[word.val + 1]! := by
              rw [hb1, getElem!_pos _ _ (by omega)]; simp only [hw1]
            show ((value ||| y) &&& 255#u64).bv.toNat = _
            rw [UScalar.bv_and, UScalar.bv_or, hvalue, hy1, ht, ← hb]
            exact bv_window_hi i1.bv b1.bv shift.val (by omega)
          · rename_i h3
            have h3' : word.val = 3 := by scalar_tac
            simp only [bind_ok, WP.spec_ok, true_and]
            simp only [show ¬ (word.val + 1 < 4) by omega, ↓reduceIte, mul_zero, add_zero]
            show (value &&& 255#u64).bv.toNat = _
            rw [UScalar.bv_and, hvalue]
            exact bv_window_lo i1.bv shift.val
        · rename_i h56
          have h56' : shift.val ≤ 56 := by scalar_tac
          simp only [WP.spec_ok, true_and]
          rw [window_lo _ _ _ h56']
          show (value &&& 255#u64).bv.toNat = _
          rw [UScalar.bv_and, hvalue]
          exact bv_window_lo i1.bv shift.val
      · rintro ⟨iter2, value1⟩ ⟨hit, hv1⟩
        simp only at hit hv1 ⊢
        subst hit
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        have hi3v : i3.val = window (wordsNat a.val) it.start.val := by
          rw [hi3, UScalar.cast_val_eq, hi2, hv1]
          exact Nat.mod_eq_of_lt (lt_of_lt_of_le (window_lt _ _) (by decide))
        step with booth_recode_w7_spec i3 as ⟨p, hd, hsg⟩
        step as ⟨a1, ha1⟩
        refine ⟨by omega, by omega, by rw [he1', he], ?_, by omega⟩
        rw [hst]
        exact windowsOk_update _ ws _ (by omega) hw p (by rw [hd, hi3v]) (by rw [hsg, hi3v]) _ rfl a1 ha1
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      rwa [show (37 : Nat) = it.start.val by omega]
  · exact ⟨hs1, hs, he, hw⟩

theorem booth_w7_spec (k : mid.p256.Scalar) :
    mid.p256.Scalar.booth_w7 k ⦃ r => WindowsOk (wordsNat k.val) r 37 ⦄ := by
  unfold mid.p256.Scalar.booth_w7
  have hl : k.val.length = 4 := k.property
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hW : wordsNat k.val % 2 ^ 64 = i.val := by
    have h := wordsNat_chunk k.val hl 0 (by norm_num)
    rw [hi, ← getElem!_pos _ _ (by omega)]
    simp only [mul_zero, pow_zero, Nat.div_one, zero_add, show 1 < 4 by norm_num, ↓reduceIte] at h
    have hb := (k.val[0]!).hBounds
    simp only [UScalarTy.numBits] at hb
    omega
  have hi3v : i3.val = window (wordsNat k.val) 0 := by
    rw [hi3, UScalar.cast_val_eq, hi2, UScalar.val_and, hi1,
      show (255#u64).val = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
    simp only [window, ↓reduceIte, pow_one]
    rw [U64.size_def]; simp only [U64.numBits, UScalarTy.numBits]
    omega
  step with booth_recode_w7_spec i3 as ⟨p, hd, hsg⟩
  step as ⟨a, ha⟩
  apply booth_w7_loop_spec k _ a (by simp) (by simp) (by simp)
  have := windowsOk_update (wordsNat k.val) (Array.repeat 37#usize (0#u8, 0#u8)) 0 (by norm_num)
    (fun i hi => absurd hi (Nat.not_lt_zero _)) p (by rw [hd, hi3v]) (by rw [hsg, hi3v]) _ rfl a ha
  simpa using this

/-! ## Points -/

/-- A number's value as a field element in Montgomery form: it times 2⁻²⁵⁶. -/
abbrev dec (x : Nat) : ZMod p256 := (p256RInv : ZMod p256) * x

theorem R_mul_RInv : ((2 ^ 256 : Nat) : ZMod p256) * (p256RInv : ZMod p256) = 1 := by
  have := congrArg (fun n : Nat => (n : ZMod p256)) p256RInv_spec.2
  simpa only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] using this

theorem RInv_ne_zero : (p256RInv : ZMod p256) ≠ 0 := fun h => by
  have := R_mul_RInv; rw [h, mul_zero] at this; exact zero_ne_one this

theorem cast_mod_p (x : Nat) : ((x % p256 : Nat) : ZMod p256) = x := ZMod.natCast_mod _ _

/-- Numbers below p are equal when their values are. -/
theorem eq_of_dec (x y : Nat) (hx : x < p256) (hy : y < p256) : x = y ↔ dec x = dec y := by
  constructor
  · intro h; rw [h]
  · intro h
    have h' : (x : ZMod p256) = y := mul_left_cancel₀ RInv_ne_zero h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
    exact h'

theorem dec_mont_mul (a b : Nat) : dec (p256RInv * a * b % p256) = dec a * dec b := by
  simp only [dec, cast_mod_p, Nat.cast_mul]; ring

theorem dec_mont_sqr (a : Nat) : dec (p256RInv * a ^ 2 % p256) = dec a ^ 2 := by
  simp only [dec, cast_mod_p, Nat.cast_mul, Nat.cast_pow]; ring

theorem val_dec (x : Nat) : p256RInv * x % p256 = (dec x).val := by
  rw [dec, ← Nat.cast_mul, ZMod.val_natCast]

theorem ofJacobian_dec (x y z : Nat) :
    p256OfJacobian (p256RInv * x % p256) (p256RInv * y % p256) (p256RInv * z % p256) =
      if dec z = 0 then none
      else some ((dec x * (dec z ^ 2)⁻¹).val, (dec y * (dec z ^ 3)⁻¹).val) := by
  unfold p256OfJacobian
  simp only [val_dec, ZMod.natCast_val, ZMod.cast_id', id, ZMod.val_eq_zero]

theorem CURVE_ONE_MONT_val : feNat mid.p256.CURVE_ONE_MONT = 2 ^ 256 % p256 := by
  simp only [feNat, mid.p256.CURVE_ONE_MONT, Array.make, wordsNat, p256]; decide

theorem dec_one : dec (2 ^ 256 % p256) = 1 := by
  rw [dec, cast_mod_p, mul_comm]; exact R_mul_RInv

theorem tripleNat_append (a b : List U64) (ha : a.length = 8) (hb : b.length = 4) :
    tripleNat (a ++ b) = ((pairNat a).1, (pairNat a).2, wordsNat b) := by
  simp [tripleNat, pairNat, List.take_append, List.drop_append, ha, hb, List.take_of_length_le]

/-- A pair of coordinates represents the point their values name. -/
theorem rep2_dec (P : P256Point) (xy : Nat × Nat) (h : p256Represents2 P xy) :
    xy.1 < p256 ∧ xy.2 < p256 ∧ P = some ((dec xy.1).val, (dec xy.2).val) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [← h3, val_dec, val_dec]⟩

/-- An affine point with a z of one in Montgomery form is the same point. -/
theorem rep_one (P : P256Point) (xy : Nat × Nat) (h : p256Represents2 P xy) :
    p256Represents P (xy.1, xy.2, 2 ^ 256 % p256) := by
  obtain ⟨h1, h2, rfl⟩ := rep2_dec P _ h
  refine ⟨h1, h2, Nat.mod_lt _ p256_pos, ?_⟩
  simp only
  rw [ofJacobian_dec, dec_one]
  simp

theorem rep_none_z (t : Nat × Nat × Nat) (h : p256Represents none t) : t.2.2 = 0 := by
  obtain ⟨-, -, hz, hP⟩ := h
  rw [ofJacobian_dec] at hP
  split_ifs at hP with h0
  · exact (eq_of_dec _ 0 hz p256_pos).mpr (by rw [h0]; simp)

theorem rep_some_z (P : P256Point) (t : Nat × Nat × Nat) (h : p256Represents P t) (hne : P ≠ none) :
    t.2.2 ≠ 0 := by
  obtain ⟨-, -, -, hP⟩ := h
  intro hz
  apply hne
  rw [← hP, hz]
  simp [p256OfJacobian]

theorem rep_zero : p256Represents none (0, 0, 0) := by
  refine ⟨p256_pos, p256_pos, p256_pos, ?_⟩
  simp [p256OfJacobian]

theorem rep2_neg (P : P256Point) (x y : Nat) (h : p256Represents2 P (x, y)) :
    p256Represents2 (p256Neg P) (x, (p256 - y) % p256) := by
  obtain ⟨hx, hy, rfl⟩ := h
  refine ⟨hx, Nat.mod_lt _ p256_pos, ?_⟩
  simp only [p256Neg, nist.neg, Option.some.injEq, Prod.mk.injEq, true_and]
  have h1 : (((p256 - y % p256) % p256 : Nat) : ZMod p256) = -(y : ZMod p256) := nist.natCast_neg_mod y
  have h2 : (((p256 - p256RInv * y % p256 % p256) % p256 : Nat) : ZMod p256) = -((p256RInv * y : Nat) : ZMod p256) :=
    by rw [Nat.mod_mod]; exact nist.natCast_neg_mod _
  simp only at hy h1
  rw [Nat.mod_eq_of_lt hy] at h1
  have L : p256RInv * ((p256 - y) % p256) % p256 = ((p256RInv * ((p256 - y) % p256) : Nat) : ZMod p256).val :=
    (ZMod.val_natCast _ _).symm
  have R : (p256 - p256RInv * y % p256 % p256) % p256 =
      (((p256 - p256RInv * y % p256 % p256) % p256 : Nat) : ZMod p256).val :=
    (ZMod.val_cast_of_lt (Nat.mod_lt _ p256_pos)).symm
  rw [L, R, h2, Nat.cast_mul, h1]
  push_cast; ring_nf

theorem fromM_inj (X Y : p256Curve.Point) (h : nist.fromM X = nist.fromM Y) : X = Y := by
  cases X <;> cases Y <;> simp [nist.fromM] at h ⊢
  exact ⟨ZMod.val_injective _ h.1, ZMod.val_injective _ h.2⟩

/-- The point `a·X`. -/
abbrev gpt (X : p256Curve.Point) (a : Int) : P256Point := nist.fromM (a • X)

theorem gpt_zero (X : p256Curve.Point) : gpt X 0 = none := by
  simp only [gpt, zero_zsmul]; rfl

theorem gpt_add (X : p256Curve.Point) (a b : Int) : p256Add (gpt X a) (gpt X b) = gpt X (a + b) := by
  simp only [gpt, p256Add, nist.fromM_add, add_zsmul]

theorem gpt_ne (X : p256Curve.Point) (hord : addOrderOf X = n256) (a b : Int) (h : ¬ a ≡ b [ZMOD n256]) :
    gpt X a ≠ gpt X b := by
  intro he
  apply h
  have := fromM_inj _ _ he
  rw [zsmul_eq_zsmul_iff_modEq, hord] at this
  exact this

/-- No point's Montgomery-form coordinates are both zero, since (0, 0) is not
on the curve. -/
theorem rep2_ne_zero (X : p256Curve.Point) (a : Int) (xy : Nat × Nat) (h : p256Represents2 (gpt X a) xy) :
    xy ≠ (0, 0) := by
  rintro rfl
  obtain ⟨-, -, h3⟩ := h
  have hc : p256OnCurve (gpt X a) := nist.onCurve_fromM _
  rw [← h3] at hc
  exact not_onCurve_zero (by simpa using hc)

theorem entry_point (X : p256Curve.Point) (hX : nist.fromM X = p256G) (w d s : Nat) :
    (if s = 0 then p256Pow p256G (2 ^ (7 * w) * d) else p256Neg (p256Pow p256G (2 ^ (7 * w) * d))) =
      gpt X (signed d s * 128 ^ w) := by
  rw [← hX, p256Pow, nist.pow_fromM, ← natCast_zsmul]
  have h128 : ((2 ^ (7 * w) * d : Nat) : Int) = (d : Int) * 128 ^ w := by
    push_cast; rw [mul_comm]; congr 1; rw [show (128 : Int) = 2 ^ 7 by norm_num, ← pow_mul]
  unfold signed
  split_ifs
  · rw [h128]
  · rw [p256Neg, nist.neg_fromM, ← neg_zsmul, h128, neg_mul]

/-- `select_w7` from row `w` of the generator table: zeros for a zero digit,
and otherwise the digit's signed multiple of 2^(7w)·G. -/
theorem select_entry (hc : RunsSelect) (X : p256Curve.Point) (hX : nist.fromM X = p256G) (w : Nat) (hw : w < 37)
    (pt : mid.p256.AffineMontPoint) (row : Std.Array U64 512#usize)
    (hrow : row = mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[w]!) (dg sg : U8) (hdg : dg.val ≤ 64) :
    mid.p256.AffineMontPoint.select_w7 pt row dg sg ⦃ r =>
      (dg.val = 0 → pairNat r.xy.val = (0, 0)) ∧
        (dg.val ≠ 0 → p256Represents2 (gpt X (signed dg.val sg.val * 128 ^ w)) (pairNat r.xy.val)) ⦄ := by
  by_cases h0 : dg.val = 0
  · have hz : pairNat (sel row dg.val) = (0, 0) := by rw [h0]; exact sel_zero row
    apply WP.spec_mono (select_w7_spec hc pt row dg sg (by rw [hz]; exact Nat.zero_le _))
    intro r hr
    refine ⟨fun _ => ?_, fun h => absurd h0 h⟩
    rw [hr, hz]
    simp
  · have hentry := tabulated w hw dg.val (by omega) hdg
    rw [← hrow] at hentry
    have hs : sel row dg.val = (row.val.drop (8 * (dg.val - 1))).take 8 := by
      simp [sel, show 1 ≤ dg.val by omega, hdg]
    rw [← pairNat_take8, ← hs] at hentry
    apply WP.spec_mono (select_w7_spec hc pt row dg sg (le_of_lt hentry.2.1))
    intro r hr
    refine ⟨fun h => absurd h h0, fun _ => ?_⟩
    rw [hr, ← entry_point X hX w dg.val sg.val]
    split_ifs with hs0
    · exact hentry
    · exact rep2_neg _ _ _ hentry

/-! ## The driver -/

theorem jac_x_spec (pt : mid.p256.JacobianMontPoint) :
    mid.p256.JacobianMontPoint.x pt ⦃ fe => fe.val = (pt.xyz.val.drop 0).take 4 ⦄ := by
  unfold mid.p256.JacobianMontPoint.x
  have hl : (pt.xyz.val).length = 12 := pt.xyz.property
  step*
  · simp [mid.p256.JacobianMontPoint.X]
  · simp [mid.p256.JacobianMontPoint.X]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.JacobianMontPoint.X]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.JacobianMontPoint.X, List.slice]

theorem jac_y_spec (pt : mid.p256.JacobianMontPoint) :
    mid.p256.JacobianMontPoint.y pt ⦃ fe => fe.val = (pt.xyz.val.drop 4).take 4 ⦄ := by
  unfold mid.p256.JacobianMontPoint.y
  have hl : (pt.xyz.val).length = 12 := pt.xyz.property
  step*
  · simp [mid.p256.JacobianMontPoint.Y]
  · simp [mid.p256.JacobianMontPoint.Y]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.JacobianMontPoint.Y]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.JacobianMontPoint.Y, List.slice]

theorem jac_z_spec (pt : mid.p256.JacobianMontPoint) :
    mid.p256.JacobianMontPoint.z pt ⦃ fe => fe.val = (pt.xyz.val.drop 8).take 4 ⦄ := by
  unfold mid.p256.JacobianMontPoint.z
  have hl : (pt.xyz.val).length = 12 := pt.xyz.property
  step*
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [mid.p256.JacobianMontPoint.Z]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.JacobianMontPoint.Z]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.JacobianMontPoint.Z, List.slice]

theorem from_affine_val (p : mid.p256.AffineMontPoint) :
    mid.p256.JacobianMontPoint.from_affine p ⦃ pt => pt.xyz.val = p.xy.val ++ mid.p256.CURVE_ONE_MONT.val ⦄ := by
  unfold mid.p256.JacobianMontPoint.from_affine core.default.DefaultArray.default
  have hl : (p.xy.val).length = 8 := p.xy.property
  step*
  · simp [mid.p256.JacobianMontPoint.XY]
  · simp [mid.p256.JacobianMontPoint.XY]
  · simp [s_post1, s1_post, mid.p256.JacobianMontPoint.XY, hl]
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [s3_post1, s4_post, mid.p256.JacobianMontPoint.Z, mid.p256.CURVE_ONE_MONT, Array.make]
  · rw [s3_post2, s5_post, s4_post, s2_post, s_post2, s1_post]
    simp only [mid.p256.JacobianMontPoint.XY, mid.p256.JacobianMontPoint.Z, Array.val_to_slice]
    generalize p.xy.val = l at hl ⊢
    match l, hl with
    | [a, b, c, d, e, f, g, h], _ =>
      simp [Array.repeat, mid.p256.CURVE_ONE_MONT, Array.make, List.setSlice!]

/-- The loop adds windows 1 to 36: each adds its digit's multiple of G to the
accumulator, which holds the sum of the windows below it. -/
theorem loop_spec (hc : RunsSelect) (X : p256Curve.Point) (hX : nist.fromM X = p256G) (hord : addOrderOf X = n256)
    (k : Nat) (hk : k < n256) (windows : Std.Array (U8 × U8) 37#usize) (hw : WindowsOk k windows 37)
    (iter : core.ops.range.Range Usize) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 37)
    (he : iter.end.val = 37) (point : mid.p256.AffineMontPoint) (a : Std.Array U64 12#usize)
    (ha : p256Represents (gpt X (acc (digit k) iter.start.val)) (tripleNat a.val)) :
    mid.p256.JacobianMontPoint.base_multiply_loop iter windows point a ⦃ r =>
      p256Represents (gpt X (acc (digit k) 37)) (tripleNat r.val) ⦄ := by
  have hk256 : k < 2 ^ 256 := lt_trans hk (by simp [n256])
  unfold mid.p256.JacobianMontPoint.base_multiply_loop
  apply loop.spec_decr_nat (fun x => 37 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 37 ∧ x.1.end.val = 37 ∧
      p256Represents (gpt X (acc (digit k) x.1.start.val)) (tripleNat x.2.2.val))
  · rintro ⟨it, pt, res⟩ ⟨hs1, hs, he, hres⟩
    simp only at hs1 hs he hres ⊢
    unfold mid.p256.JacobianMontPoint.base_multiply_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have he1' : iter1.end.val = it.end.val := by rw [he1]
      step as ⟨pr, hpr⟩
      obtain ⟨dg, sg⟩ := pr
      step as ⟨row, hrow⟩
      set w := it.start.val with hwdef
      have hwk := hw w (by omega)
      have hpr' : windows.val[w]! = (dg, sg) := by
        rw [getElem!_pos _ _ (by rw [windows.property]; scalar_tac)]; exact hpr.symm
      rw [hpr'] at hwk
      obtain ⟨hdg, hsg⟩ := hwk
      simp only at hdg hsg
      have hdig : digit k w = signed dg.val sg.val := by rw [digit, hdg, hsg]
      have hd64 : dg.val ≤ 64 := by rw [hdg]; exact boothD_le _ (window_lt _ _)
      have hrow' : row = mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[w]! := by
        rw [hrow, getElem!_pos _ _ (by rw [Std.Array.property]; scalar_tac)]
      step with select_entry hc X hX w (by omega) pt row hrow' dg sg hd64 as ⟨pt1, hz, hP2⟩
      step as ⟨r1, hr1⟩
      obtain ⟨hX1, hY1, hZ1, -⟩ := id hres
      have hacc : acc (digit k) iter1.start.val = acc (digit k) w + digit k w * 128 ^ w := by
        rw [hst, acc_succ]
      refine ⟨by omega, by omega, by rw [he1', he], ?_, by omega⟩
      rw [hacc]
      by_cases hd0 : dg.val = 0
      · have hz' := hz hd0
        have hd : digit k w = 0 := by rw [hdig, hd0]; simp [signed]
        rw [hd, zero_mul, add_zero,
          (hr1 hX1 hY1 hZ1 (by rw [hz']; exact p256_pos) (by rw [hz']; exact p256_pos)).1 hz']
        exact hres
      · have hP2' := hP2 hd0
        rw [← hdig] at hP2'
        have hne0 := rep2_ne_zero X _ _ hP2'
        have hr := hr1 hX1 hY1 hZ1 hP2'.1 hP2'.2.1
        have hdne : digit k w ≠ 0 := by rw [hdig]; unfold signed; split <;> omega
        by_cases hA : acc (digit k) w = 0
        · rw [hA] at hres ⊢
          rw [gpt_zero] at hres
          have hz0 := rep_none_z _ hres
          rw [hr.2.1 hne0 hz0, zero_add]
          exact rep_one _ _ hP2'
        · have hne : gpt X (acc (digit k) w) ≠ none := by
            rw [← gpt_zero X]
            exact gpt_ne X hord _ _ (fun h => hA (acc_modEq_zero _ (fun w _ => digit_abs k w) w (by omega) h))
          have hP12 := gpt_ne X hord _ _ (booth_ne (digit k) (fun w _ => digit_abs k w) (digit_36 k hk256) k
            (booth_sum k hk256) hk w (by omega) hdne)
          rw [← gpt_add]
          exact hr.2.2 hne0 (rep_some_z _ _ hres hne) _ _ hres hP2' hP12
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      rwa [show (37 : Nat) = it.start.val by omega]
  · exact ⟨hs1, hs, he, ha⟩

/-- x86_64's Jacobian `base_multiply` represents k·G, for k below n. -/
theorem jac_base_multiply_spec (hc : RunsSelect) (k : mid.p256.Scalar) (hk : wordsNat k.val < n256) :
    mid.p256.JacobianMontPoint.base_multiply k ⦃ r =>
      p256Represents (p256Pow p256G (wordsNat k.val)) (tripleNat r.xyz.val) ⦄ := by
  obtain ⟨X, hX, hX0, hn⟩ := fromM_G
  have hord : addOrderOf X = n256 := addOrderOf_eq_prime hn hX0
  have hk256 : wordsNat k.val < 2 ^ 256 := lt_trans hk (by simp [n256])
  unfold mid.p256.JacobianMontPoint.base_multiply mid.p256.AffineMontPoint.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step with booth_w7_spec k as ⟨windows, hw⟩
  step as ⟨pr, hpr⟩
  obtain ⟨dg, sg⟩ := pr
  step as ⟨row, hrow⟩
  have hwk := hw 0 (by norm_num)
  have hpr' : windows.val[0]! = (dg, sg) := by
    rw [getElem!_pos _ _ (by rw [windows.property]; scalar_tac)]; exact hpr.symm
  rw [hpr'] at hwk
  obtain ⟨hdg, hsg⟩ := hwk
  simp only at hdg hsg
  have hdig : digit (wordsNat k.val) 0 = signed dg.val sg.val := by rw [digit, hdg, hsg]
  have hd64 : dg.val ≤ 64 := by rw [hdg]; exact boothD_le _ (window_lt _ _)
  have hrow' : row = mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[0]! := by
    rw [hrow, getElem!_pos _ _ (by rw [Std.Array.property]; scalar_tac)]
  step with select_entry hc X hX 0 (by norm_num) _ row hrow' dg sg hd64 as ⟨pt1, hz, hP2⟩
  step with from_affine_val pt1 as ⟨res, hres⟩
  step*
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [s1_post, s_post1, mid.p256.JacobianMontPoint.Z]
  · simp [s2_post, s_post1, mid.p256.JacobianMontPoint.Z]
  · have hn := from_u8_val dg
    have hZ : mid.p256.JacobianMontPoint.Z = { start := 8#usize, «end» := 12#usize } := by
      simp [mid.p256.JacobianMontPoint.Z]
    have hsl : s3.val.length = 4 := by
      have : s3.length = 4 := by rw [s3_post, s_post1, hZ]; rfl
      simpa [Slice.length] using this
    have hv : (index_mut_back s3).val = pt1.xy.val ++ s3.val := by
      rw [s_post2, hZ, hres]
      simp only
      have h8 : pt1.xy.val.length = 8 := pt1.xy.property
      generalize pt1.xy.val = l at h8 ⊢
      match l, h8 with
      | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
        generalize s3.val = q at hsl ⊢
        match q, hsl with
        | [b0, b1, b2, b3], _ =>
          simp [List.setSlice!, mid.p256.CURVE_ONE_MONT, Array.make]
    have hz3 : wordsNat s3.val = if dg.val ≠ 0 then 2 ^ 256 % p256 else 0 := by
      rw [s3_post1, hn, s1_post, s2_post]
      simp only [Array.val_to_slice]
      split_ifs
      · exact CURVE_ONE_MONT_val
      · simp [Array.repeat, wordsNat, Nat.ofDigits]
    have htrip : tripleNat (index_mut_back s3).val =
        ((pairNat pt1.xy.val).1, (pairNat pt1.xy.val).2, if dg.val ≠ 0 then 2 ^ 256 % p256 else 0) := by
      rw [hv, tripleNat_append _ _ pt1.xy.property hsl, hz3]
    have hinit : p256Represents (gpt X (acc (digit (wordsNat k.val)) 1)) (tripleNat (index_mut_back s3).val) := by
      rw [htrip]
      have h1 : acc (digit (wordsNat k.val)) 1 = signed dg.val sg.val := by simp [acc, hdig]
      rw [h1]
      by_cases hd0 : dg.val = 0
      · simp only [hd0, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [hz hd0]
        simp only [signed, Nat.cast_zero, neg_zero, ite_self, gpt_zero]
        exact rep_zero
      · simp only [hd0, ne_eq, not_false_eq_true, ↓reduceIte]
        have := hP2 hd0
        simp only [pow_zero, mul_one] at this
        exact rep_one _ _ this
    step with loop_spec hc X hX hord (wordsNat k.val) hk windows hw { start := 1#usize, «end» := 37#usize }
      (by simp) (by simp) (by simp) pt1 (index_mut_back s3) (by simpa using hinit)
      as ⟨a4, ha4⟩
    rw [show acc (digit (wordsNat k.val)) 37 = wordsNat k.val from booth_sum _ hk256] at ha4
    rw [← hX, p256Pow, nist.pow_fromM, ← natCast_zsmul]
    exact ha4

/-! ## Affine conversion -/

theorem fe_inv_spec (a : mid.p256.FieldElement) :
    mid.p256.FieldElement.inv a ⦃ r => feNat r < p256 ∧
      (feNat a % p256 = 0 → feNat r = 0) ∧ (feNat a % p256 ≠ 0 → feNat a * feNat r % p256 = 1) ⦄ := by
  unfold mid.p256.FieldElement.inv mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

/-- A finite point's Jacobian coordinates, as their values: z is nonzero and
the point is (x/z², y/z³). -/
theorem rep_some (P : P256Point) (t : Nat × Nat × Nat) (h : p256Represents P t) (hne : P ≠ none) :
    t.1 < p256 ∧ t.2.1 < p256 ∧ t.2.2 < p256 ∧ dec t.2.2 ≠ 0 ∧
      P = some ((dec t.1 * (dec t.2.2 ^ 2)⁻¹).val, (dec t.2.1 * (dec t.2.2 ^ 3)⁻¹).val) := by
  obtain ⟨hX, hY, hZ, hP⟩ := h
  rw [ofJacobian_dec] at hP
  have hZ0 : dec t.2.2 ≠ 0 := fun h0 => by
    rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)] at hP; exact hne hP.symm
  rw [ite_eq_right_iff.mpr (fun h => absurd h hZ0)] at hP
  exact ⟨hX, hY, hZ, hZ0, hP.symm⟩

theorem as_affine_by_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (P : P256Point)
    (h : p256Represents P (tripleNat pt.xyz.val)) (hne : P ≠ none)
    (zi : mid.p256.FieldElement) (hzi : feNat zi < p256)
    (hinv : dec (feNat zi) = (dec (tripleNat pt.xyz.val).2.2)⁻¹) :
    mid.p256.JacobianMontPoint.as_affine_by pt zi ⦃ a => p256Represents2 P (pairNat a.xy.val) ⦄ := by
  obtain ⟨hX, hY, hZ, hZ0, rfl⟩ := rep_some P _ h hne
  have hlt : ∀ x, x % p256 < p256 := fun x => Nat.mod_lt _ p256_pos
  unfold mid.p256.JacobianMontPoint.as_affine_by
  step with mont_sqr_spec _hr zi hzi as ⟨z2, hz2⟩
  step with mont_mul_spec _hr z2 zi (by rw [hz2]; exact hlt _) hzi as ⟨z3, hz3⟩
  step with jac_x_spec pt as ⟨fx, hfx⟩
  have hfxX : feNat fx = (tripleNat pt.xyz.val).1 := by simp [tripleNat, feNat, hfx]
  step with mont_mul_spec _hr fx z2 (by rw [hfxX]; exact hX) (by rw [hz2]; exact hlt _) as ⟨x, hx⟩
  step with jac_y_spec pt as ⟨fy, hfy⟩
  have hfyY : feNat fy = (tripleNat pt.xyz.val).2.1 := by simp [tripleNat, feNat, hfy]
  step with mont_mul_spec _hr fy z3 (by rw [hfyY]; exact hY) (by rw [hz3]; exact hlt _) as ⟨y, hy⟩
  step as ⟨a, ha⟩
  rw [ha, pairNat_append _ _ x.property y.property]
  refine ⟨by rw [show wordsNat x.val = feNat x from rfl, hx]; exact hlt _,
    by rw [show wordsNat y.val = feNat y from rfl, hy]; exact hlt _, ?_⟩
  rw [show wordsNat x.val = feNat x from rfl, show wordsNat y.val = feNat y from rfl, val_dec, val_dec, hx, hy,
    dec_mont_mul, dec_mont_mul, hz3, hz2, dec_mont_mul, dec_mont_sqr, hinv, hfxX, hfyY]
  congr 3 <;> field_simp

/-- With a zero inverse, infinity's, `as_affine_by` gives zeros. -/
theorem as_affine_by_zero (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (hX : (tripleNat pt.xyz.val).1 < p256)
    (hY : (tripleNat pt.xyz.val).2.1 < p256) (zi : mid.p256.FieldElement) (hzi : feNat zi = 0) :
    mid.p256.JacobianMontPoint.as_affine_by pt zi ⦃ a => pairNat a.xy.val = (0, 0) ⦄ := by
  unfold mid.p256.JacobianMontPoint.as_affine_by
  have hz : feNat zi < p256 := by rw [hzi]; exact p256_pos
  step with mont_sqr_spec _hr zi hz as ⟨z2, hz2⟩
  have hz2' : feNat z2 = 0 := by rw [hz2, hzi]; simp
  step with mont_mul_spec _hr z2 zi (by rw [hz2']; exact p256_pos) hz as ⟨z3, hz3⟩
  have hz3' : feNat z3 = 0 := by rw [hz3, hzi]; simp
  step with jac_x_spec pt as ⟨fx, hfx⟩
  have hfxX : feNat fx = (tripleNat pt.xyz.val).1 := by simp [tripleNat, feNat, hfx]
  step with mont_mul_spec _hr fx z2 (by rw [hfxX]; exact hX) (by rw [hz2']; exact p256_pos) as ⟨x, hx⟩
  step with jac_y_spec pt as ⟨fy, hfy⟩
  have hfyY : feNat fy = (tripleNat pt.xyz.val).2.1 := by simp [tripleNat, feNat, hfy]
  step with mont_mul_spec _hr fy z3 (by rw [hfyY]; exact hY) (by rw [hz3']; exact p256_pos) as ⟨y, hy⟩
  step as ⟨a, ha⟩
  rw [ha, pairNat_append _ _ x.property y.property]
  rw [show wordsNat x.val = feNat x from rfl, show wordsNat y.val = feNat y from rfl, hx, hy, hz2', hz3']
  simp

theorem tomont_rinv (x : Nat) (hx : x < p256) : 2 ^ 256 * (p256RInv * x % p256) % p256 = x := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod, p256RInv_spec.2, one_mul,
    Nat.mod_mod, Nat.mod_eq_of_lt hx]

theorem pow_onCurve (n : Nat) : p256OnCurve (p256Pow p256G n) := by
  obtain ⟨X, hX, -, -⟩ := fromM_G
  rw [← hX, p256Pow, nist.pow_fromM]
  exact nist.onCurve_fromM _

/-- x86_64's `base_multiply` computes k·G for k below n, as aarch64's
s2n-bignum `p256_scalarmulbase` does for every k: Montgomery-form
coordinates, and zeros for infinity. -/
theorem base_multiply_spec (_hr : Runs) (k : mid.p256.Scalar) (hk : wordsNat k.val < n256) :
    mid.p256.AffineMontPoint.base_multiply k ⦃ q =>
      ∃ rx ry, p256AffineZ (rx, ry) (p256Pow p256G (wordsNat k.val)) ∧
        pairNat q.xy.val = (2 ^ 256 * rx % p256, 2 ^ 256 * ry % p256) ⦄ := by
  unfold mid.p256.AffineMontPoint.base_multiply mid.p256.JacobianMontPoint.as_affine
  step with jac_base_multiply_spec (runsSelect_of_runs _hr) k hk as ⟨jac, hjac⟩
  step with jac_z_spec jac as ⟨fz, hfz⟩
  have hzf : feNat fz = (tripleNat jac.xyz.val).2.2 := by simp [tripleNat, feNat, hfz]
  obtain ⟨hX, hY, hZ, -⟩ := id hjac
  step with demont_spec _hr fz (by rw [hzf]; exact hZ) as ⟨fz1, hfz1⟩
  step with fe_inv_spec fz1 as ⟨fz2, hlt2, h0, h1⟩
  step with as_mont_spec _hr fz2 as ⟨fz3, hfz3⟩
  by_cases hP0 : p256Pow p256G (wordsNat k.val) = none
  · rw [hP0] at hjac
    have hz0 : (tripleNat jac.xyz.val).2.2 = 0 := rep_none_z _ hjac
    have e1 : feNat fz1 = 0 := by rw [hfz1, hzf, hz0]; simp
    have e2 : feNat fz2 = 0 := h0 (by rw [e1]; simp)
    have e3 : feNat fz3 = 0 := by rw [hfz3, e2]; simp
    apply WP.spec_mono (as_affine_by_zero _hr jac hX hY fz3 e3)
    intro q hq
    refine ⟨0, 0, ?_, ?_⟩
    · rw [hP0]; simp [p256AffineZ]
    · rw [hq]; simp
  · obtain ⟨-, -, -, hZ0, -⟩ := rep_some _ _ hjac hP0
    have hfz1d : ((feNat fz1 : Nat) : ZMod p256) = dec (tripleNat jac.xyz.val).2.2 := by
      rw [hfz1, cast_mod_p, Nat.cast_mul, hzf]
    have hne : feNat fz1 % p256 ≠ 0 := by
      intro h
      apply hZ0
      rw [← hfz1d, ← cast_mod_p (feNat fz1), h, Nat.cast_zero]
    have hm : (feNat fz1 : ZMod p256) * (feNat fz2 : ZMod p256) = 1 := by
      have := congrArg (fun n : Nat => (n : ZMod p256)) (h1 hne)
      simpa only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] using this
    have hfz2 : (feNat fz2 : ZMod p256) = (feNat fz1 : ZMod p256)⁻¹ := eq_inv_of_mul_eq_one_right hm
    have hinv : dec (feNat fz3) = (dec (tripleNat jac.xyz.val).2.2)⁻¹ := by
      show (p256RInv : ZMod p256) * ((feNat fz3 : Nat) : ZMod p256) = _
      rw [hfz3, cast_mod_p, Nat.cast_mul, ← mul_assoc, mul_comm (p256RInv : ZMod p256), R_mul_RInv, one_mul,
        hfz2, hfz1d]
    apply WP.spec_mono (as_affine_by_spec _hr jac _ hjac hP0 fz3 (by rw [hfz3]; exact Nat.mod_lt _ p256_pos) hinv)
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    refine ⟨p256RInv * (pairNat q.xy.val).1 % p256, p256RInv * (pairNat q.xy.val).2 % p256, ?_, ?_⟩
    · unfold p256AffineZ
      split_ifs with h00
      · exfalso
        have hc := pow_onCurve (wordsNat k.val)
        simp only at h00
        rw [← hq3, h00.1, h00.2] at hc
        exact not_onCurve_zero hc
      · rw [← hq3, Nat.mod_mod, Nat.mod_mod]
    · rw [tomont_rinv _ hq1, tomont_rinv _ hq2]

end P256Base

/-! ## What the shared proofs take

`Rind.X86_64.P256` and those above it, which `admin/prove` also writes for
aarch64, name these as aarch64's `Rind.Aarch64.P256Base` states them. -/

namespace P256

@[step]
theorem base_multiply_spec (_hr : Runs) (k : mid.p256.Scalar) (hk : wordsNat k.val < n256) :
    mid.p256.AffineMontPoint.base_multiply k ⦃ q =>
      ∃ rx ry, p256AffineZ (rx, ry) (p256Pow p256G (wordsNat k.val)) ∧
        pairNat q.xy.val = (2 ^ 256 * rx % p256, 2 ^ 256 * ry % p256) ⦄ :=
  P256Base.base_multiply_spec _hr k hk

/-- The generator table's first row holds G to 32G. -/
theorem first_row : ∀ j, 1 ≤ j → j ≤ 32 →
    p256Represents2 (p256Pow p256G j) (pairNat ((mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[0]!).val.drop (8 * (j - 1)))) :=
  P256Base.first_row

end P256

end rind.x86_64
