import Rind.Portable.Mont
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# The portable backend's word routines on RSA verification's path

`low::generic::bignum`'s comparison, bit length, and `-x⁻¹ mod 2^64`, which
x86_64 takes from s2n-bignum's theorems as axioms, each proven here against
`Nat` arithmetic on the limbs `wordsNat` reads, in the shapes those axioms
state, so that the RSA proofs `admin/prove` writes from x86_64's run on them.
-/

namespace rind.portable

/-! ## Masks -/

/-- A nonzero word or its negation reaches the top bit. -/
theorem nonzero_top (x : BitVec 64) (hx : x.toNat ≠ 0) : (x ||| -x).toNat >>> 63 = 1 := by
  have hlt := x.isLt
  rw [BitVec.toNat_or, BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - x.toNat < 2 ^ 64)]
  have h1 : x.toNat ≤ x.toNat ||| (2 ^ 64 - x.toNat) := Nat.left_le_or
  have h2 : 2 ^ 64 - x.toNat ≤ x.toNat ||| (2 ^ 64 - x.toNat) := Nat.right_le_or
  have h3 : x.toNat ||| (2 ^ 64 - x.toNat) < 2 ^ 64 := Nat.or_lt_two_pow hlt (by omega)
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- `nonzero`: one for a nonzero word, zero for zero. -/
@[step]
theorem nonzero_spec (x : U64) :
    low.generic.bignum.nonzero x ⦃ r => r.val = if x.val = 0 then 0 else 1 ⦄ := by
  unfold low.generic.bignum.nonzero core.num.U64.wrapping_neg
  simp only [lift, bind_ok]
  step as ⟨r, hr⟩
  rw [hr]
  split
  · rename_i h
    have : x = 0#u64 := UScalar.eq_of_val_eq (by simpa using h)
    subst this
    rfl
  · rename_i h
    show (x.bv ||| -x.bv).toNat >>> 63 = 1
    exact nonzero_top x.bv h

/-- `select`: `x` for the bit one, `y` for zero. -/
@[step]
theorem select_spec (bit x y : U64) (hb : bit.val ≤ 1) :
    low.generic.bignum.select bit x y ⦃ r => r = if bit.val = 0 then y else x ⦄ := by
  unfold low.generic.bignum.select low.generic.bignum.mask core.hint.black_box
  simp only [lift, bind_ok, WP.spec_ok]
  have hm := and_mask_val (x ^^^ y) _ (neg_bit_mask bit hb)
  rw [neg_bit_val bit hb] at hm
  apply UScalar.eq_of_val_eq
  rcases (show bit.val = 0 ∨ bit.val = 1 by omega) with h | h
  · simp only [h, ↓reduceIte] at hm ⊢
    rw [UScalar.val_xor, hm, Nat.xor_zero]
  · simp only [h, show (2 : Nat) ^ 64 - 1 ≠ 0 by norm_num, one_ne_zero, ↓reduceIte, UScalar.val_xor] at hm ⊢
    rw [hm, Nat.xor_comm x.val y.val, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ## Words beyond a slice -/

/-- `word`: `x`'s `i`th word, or zero past its end. -/
@[step]
theorem word_spec (x : Slice U64) (i : Usize) :
    low.generic.bignum.word x i ⦃ r => r.val = if i.val < x.length then x.val[i.val]!.val else 0 ⦄ := by
  unfold low.generic.bignum.word core.slice.Slice.get core.option.OptionShared0T.copied
  simp only [core.slice.index.Usize.get, bind_ok, WP.spec_ok]
  split
  · rename_i h
    rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem (by simpa [Slice.length] using h)]
    simp [getElem!_pos x.val i.val (by simpa [Slice.length] using h)]
  · rename_i h
    rw [Slice.getElem?_Usize_eq, List.getElem?_eq_none (by simp [Slice.length] at h ⊢; omega)]
    simp

/-- Extending a prefix by a word, or by zero once past the end. -/
theorem wordsNat_take_succ_word (l : List U64) (j : Nat) :
    wordsNat (l.take (j + 1)) = wordsNat (l.take j) + 2 ^ (64 * j) * (if j < l.length then l[j]!.val else 0) := by
  split
  · exact wordsNat_take_succ' l j (by assumption)
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]; simp

/-! ## `bignum_cmp_lt` -/

theorem cmp_lt_loop_spec (x y : Slice U64)
    (iter : core.ops.range.Range Usize) (borrow : U64)
    (hend : iter.end.val = max x.length y.length) (hi : iter.start.val ≤ iter.end.val) (hb : borrow.val ≤ 1)
    (hinv : ∃ D : Nat, D < 2 ^ (64 * iter.start.val) ∧
      (D : Int) - 2 ^ (64 * iter.start.val) * borrow.val =
        wordsNat (x.val.take iter.start.val) - wordsNat (y.val.take iter.start.val)) :
    low.generic.bignum.bignum_cmp_lt_loop iter x y borrow ⦃ r =>
      r.val = if wordsNat x.val < wordsNat y.val then 1 else 0 ⦄ := by
  unfold low.generic.bignum.bignum_cmp_lt_loop
  apply loop.spec_decr_nat (fun x' => max x.length y.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × U64 =>
      x'.1.end.val = max x.length y.length ∧ x'.1.start.val ≤ max x.length y.length ∧ x'.2.val ≤ 1 ∧
      ∃ D : Nat, D < 2 ^ (64 * x'.1.start.val) ∧
        (D : Int) - 2 ^ (64 * x'.1.start.val) * x'.2.val =
          wordsNat (x.val.take x'.1.start.val) - wordsNat (y.val.take x'.1.start.val))
  · rintro ⟨it, bw⟩ ⟨he, hs, hb, D, hD, hv⟩
    simp only at he hs hb hD hv
    unfold low.generic.bignum.bignum_cmp_lt_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = max x.length y.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv hD
      have hxl : x.val.length = x.length := rfl
      have hyl : y.val.length = y.length := rfl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hv
      have hD' : (D : Int) < 2 ^ (64 * max x.length y.length) := by exact_mod_cast hD
      have hX := wordsNat_lt' x.val
      have hY := wordsNat_lt' y.val
      have hXm : (2 : Int) ^ (64 * x.val.length) ≤ 2 ^ (64 * max x.length y.length) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hYm : (2 : Int) ^ (64 * y.val.length) ≤ 2 ^ (64 * max x.length y.length) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hX' : (wordsNat x.val : Int) < 2 ^ (64 * x.val.length) := by exact_mod_cast hX
      have hY' : (wordsNat y.val : Int) < 2 ^ (64 * y.val.length) := by exact_mod_cast hY
      have hb' : bw.val = 0 ∨ bw.val = 1 := by omega
      rcases hb' with h | h <;> rw [h] at hv ⊢ <;> split_ifs with hlt <;>
        first | rfl | (exfalso; push_cast at hv; omega)
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      step as ⟨xi, hxi⟩
      step as ⟨yi, hyi⟩
      step as ⟨diff, b1, hd1⟩
      step as ⟨diff1, b2, hd2⟩
      simp only [lift, bind_ok, WP.spec_ok]
      have hstep := sub_step xi.val yi.val bw.val diff.val diff1.val b1 b2 xi.hBounds yi.hBounds hb
        (by simpa [u64_size] using hd1) (by simpa [u64_size] using hd2)
      rw [← from_bool_val] at hstep
      have hc := sub_chain_step it.start.val hv hstep
      refine ⟨by rw [hend1, he], by omega, by rw [from_bool_val]; cases (b1 || b2) <;> simp,
        ⟨D + 2 ^ (64 * it.start.val) * diff1.val, ?_, ?_⟩, by omega⟩
      · rw [hst, show 64 * (it.start.val + 1) = 64 * it.start.val + 64 by ring, pow_add]
        have := diff1.hBounds
        simp only [UScalarTy.numBits] at this
        nlinarith
      · have ex : (if it.start.val < x.val.length then x.val[it.start.val]!.val else 0) = xi.val := by
          rw [hxi]
        have ey : (if it.start.val < y.val.length then y.val[it.start.val]!.val else 0) = yi.val := by
          rw [hyi]
        rw [hst, wordsNat_take_succ_word, wordsNat_take_succ_word, ex, ey]
        push_cast
        linarith
  · exact ⟨hend, by simp only; omega, hb, hinv⟩

/-- `BIGNUM_LT_SUBROUTINE_CORRECT`'s statement, as x86_64's axiom states it. -/
@[step]
theorem bignum_cmp_lt_spec (x y : Slice U64) :
    low.generic.bignum.bignum_cmp_lt x y ⦃ r =>
      r.val = if wordsNat x.val < wordsNat y.val then 1 else 0 ⦄ := by
  unfold low.generic.bignum.bignum_cmp_lt
  simp only [lift, bind_ok]
  exact cmp_lt_loop_spec x y { start := 0#usize, «end» := core.cmp.impls.OrdUsize.max x.len y.len } 0#u64
    (by simp [core.cmp.impls.OrdUsize.max_val]) (by simp) (by simp) ⟨0, by simp, by simp [wordsNat_nil]⟩

/-! ## `bignum_bitsize` -/

/-- A nonzero word above `i` words adds its bits to theirs. -/
theorem size_add_top (X w i : Nat) (hX : X < 2 ^ (64 * i)) (hw : 0 < w) :
    (X + 2 ^ (64 * i) * w).size = 64 * i + w.size := by
  apply le_antisymm
  · apply Nat.size_le.mpr
    rw [pow_add]
    have := Nat.lt_size_self w
    calc X + 2 ^ (64 * i) * w < 2 ^ (64 * i) + 2 ^ (64 * i) * w := by omega
      _ = 2 ^ (64 * i) * (w + 1) := by ring
      _ ≤ 2 ^ (64 * i) * 2 ^ w.size := Nat.mul_le_mul_left _ this
  · have hs : 1 ≤ w.size := Nat.size_pos.mpr hw
    have hw2 := Nat.lt_size.mp (show w.size - 1 < w.size by omega)
    have : 64 * i + (w.size - 1) < (X + 2 ^ (64 * i) * w).size := by
      apply Nat.lt_size.mpr
      rw [pow_add]
      calc 2 ^ (64 * i) * 2 ^ (w.size - 1) ≤ 2 ^ (64 * i) * w := Nat.mul_le_mul_left _ hw2
        _ ≤ X + 2 ^ (64 * i) * w := by omega
    omega

/-- A word's bits: 64 less its leading zeros. -/
theorem size_eq_log (w : Nat) (hw : w ≠ 0) : w.size = Nat.log 2 w + 1 := by
  apply le_antisymm
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) w)
  · exact Nat.lt_size.mpr (Nat.pow_log_le_self 2 hw)

theorem size_word (w : U64) (hw : w.val ≠ 0) :
    64 - (core.num.U64.leading_zeros w).val = w.val.size := by
  have hlt := w.hBounds
  simp only [UScalarTy.numBits] at hlt
  have hbv : w.bv ≠ 0 := by intro h; apply hw; show w.bv.toNat = 0; rw [h]; rfl
  have hlog : Nat.log 2 w.val < 64 := Nat.log_lt_of_lt_pow hw (by simpa using hlt)
  rw [size_eq_log _ hw]
  simp only [core.num.U64.leading_zeros, BitVec.leadingZeros, hbv, ↓reduceIte]
  show 64 - (BitVec.ofNat 32 (64 - Nat.log 2 w.bv.toNat - 1)).toNat = _
  rw [BitVec.toNat_ofNat]
  show 64 - (64 - Nat.log 2 w.val - 1) % 2 ^ 32 = _
  omega

theorem bitsize_loop_spec (x : Slice U64) (hx : x.length < 2 ^ 26)
    (iter : core.ops.range.Range Usize) (bits : U64)
    (hend : iter.end.val = x.length) (hi : iter.start.val ≤ x.length)
    (hinv : bits.val = (wordsNat (x.val.take iter.start.val)).size) :
    low.generic.bignum.bignum_bitsize_loop iter x bits ⦃ r => r.val = (wordsNat x.val).size ⦄ := by
  unfold low.generic.bignum.bignum_bitsize_loop
  apply loop.spec_decr_nat (fun x' => x.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × U64 =>
      x'.1.end.val = x.length ∧ x'.1.start.val ≤ x.length ∧
      x'.2.val = (wordsNat (x.val.take x'.1.start.val)).size)
  · rintro ⟨it, bw⟩ ⟨he, hs, hv⟩
    simp only at he hs hv
    unfold low.generic.bignum.bignum_bitsize_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = x.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [hv, h0, List.take_of_length_le (by simp [Slice.length])]
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hlt' : it.start.val < x.val.length := hlt
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = it.start.val := by
        rw [hi1, UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      simp only [lift_eq, bind_ok]
      step as ⟨i7, hi7⟩
      step as ⟨bits1, hb1⟩
      · split at hi7 <;> omega
      refine ⟨by rw [hend1, he], by omega, ?_, by omega⟩
      have hw : i4 = x.val[it.start.val]! := by rw [hi4, getElem!_pos x.val _ hlt']
      rw [hst, wordsNat_take_succ' _ _ hlt', ← hw, hb1]
      by_cases h0 : i4.val = 0
      · simp only [h0, ↓reduceIte] at hi7
        simp only [hi7, ↓reduceIte, h0, Nat.mul_zero, Nat.add_zero, hv]
      · simp only [h0, ↓reduceIte] at hi7
        simp only [hi7, one_ne_zero, ↓reduceIte, core.num.U64.wrapping_sub_val_eq,
          core.convert.num.FromU64U32.from_val_eq]
        have hX : wordsNat (x.val.take it.start.val) < 2 ^ (64 * it.start.val) := by
          have := wordsNat_lt' (x.val.take it.start.val)
          rwa [List.length_take, Nat.min_eq_left hlt'.le] at this
        rw [size_add_top _ _ _ hX (Nat.pos_of_ne_zero h0), ← size_word i4 h0, hi5]
        have hlz : (core.num.U64.leading_zeros i4).val ≤ 64 := by
          have h1 := size_word i4 h0
          have h2 : 0 < i4.val.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
          omega
        have hA : i3.val = it.start.val * 64 + 64 := by rw [hi3, hi2, hi1v]
        have hsz : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [u64_size]
        have hlen : it.start.val < 2 ^ 26 := by simp only [Slice.length] at hlt hx; omega
        rw [hA, hsz]
        rw [show it.start.val * 64 + 64 + (2 ^ 64 - (core.num.U64.leading_zeros i4).val) =
          (it.start.val * 64 + 64 - (core.num.U64.leading_zeros i4).val) + 2 ^ 64 by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
  · exact ⟨hend, hi, hinv⟩

/-- `BIGNUM_BITSIZE_SUBROUTINE_CORRECT`'s statement, as x86_64's axiom
states it, for a slice of under `2^26` words, whose bit count fits a word. -/
@[step]
theorem bignum_bitsize_spec (x : Slice U64) (hx : x.length < 2 ^ 26) :
    low.generic.bignum.bignum_bitsize x ⦃ r => r.val = (wordsNat x.val).size ⦄ := by
  unfold low.generic.bignum.bignum_bitsize
  step with bitsize_loop_spec x hx { start := 0#usize, «end» := Slice.len x } 0#u64 (by simp) (by simp)
    (by simp [wordsNat_nil]) as ⟨b, hb⟩
  rw [UScalar.cast_val_eq, hb]
  have h32 : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; cases System.Platform.numBits_eq <;> simp_all
  have hs : (wordsNat x.val).size ≤ 64 * x.length := Nat.size_le.mpr (wordsNat_lt' x.val)
  exact Nat.mod_eq_of_lt (by omega)

/-! ## `bignum_negmodinv` -/

/-- XOR acts on the low `k` bits alone. -/
theorem xor_mod_pow (a b k : Nat) : (a ^^^ b) % 2 ^ k = (a % 2 ^ k) ^^^ (b % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases h : i < k <;> simp [h]

/-- The first guess, `3x ⊕ 2`, is `x⁻¹` modulo `2^5` for an odd `x`. -/
theorem newton_start (x : Nat) (hx : x % 2 = 1) :
    (32 : Int) ∣ (x : Int) * (((x * 3 % 2 ^ 64) ^^^ 2 : Nat) : Int) - 1 := by
  have h32 : (32 : Nat) = 2 ^ 5 := rfl
  have : x * ((x * 3 % 2 ^ 64) ^^^ 2) % 32 = 1 := by
    rw [Nat.mul_mod, h32, xor_mod_pow, Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 5 ∣ 2 ^ 64), ← h32,
      Nat.mul_mod x 3]
    have hr : x % 32 < 32 := Nat.mod_lt _ (by norm_num)
    have hodd : x % 32 % 2 = 1 := by omega
    generalize x % 32 = r at hr hodd
    revert r; decide
  have h' : ((x : Int) * (((x * 3 % 2 ^ 64) ^^^ 2 : Nat) : Int)) % 32 = 1 := by exact_mod_cast this
  exact Int.ModEq.dvd (show (1 : Int) % 32 = _ % 32 by rw [h']; rfl)

/-- Newton's step, `a·(2 - x·a)` modulo `2^64`, doubles the low bits in
which `x·a` is one, up to all 64. -/
theorem newton_step (x a k : Nat) (h : (2 : Int) ^ k ∣ (x : Int) * a - 1) :
    (2 : Int) ^ min (2 * k) 64 ∣
      (x : Int) * ((a * ((2 + (2 ^ 64 - x * a % 2 ^ 64)) % 2 ^ 64) % 2 ^ 64 : Nat) : Int) - 1 := by
  have hle : x * a % 18446744073709551616 ≤ 18446744073709551616 := (Nat.mod_lt _ (by norm_num)).le
  push_cast [Nat.cast_sub hle]
  rw [show (18446744073709551616 : Int) = 2 ^ 64 by norm_num]
  have h0 : (2 : Int) ^ 64 ≡ 0 [ZMOD 2 ^ 64] := by simp [Int.ModEq]
  have h1 : ((2 : Int) + (2 ^ 64 - (x : Int) * a % 2 ^ 64)) % 2 ^ 64 ≡ 2 - x * a [ZMOD 2 ^ 64] := by
    refine (Int.mod_modEq _ _).trans ?_
    calc (2 : Int) + (2 ^ 64 - (x : Int) * a % 2 ^ 64) ≡ 2 + (0 - x * a) [ZMOD 2 ^ 64] :=
          (h0.sub (Int.mod_modEq _ _)).add_left 2
      _ = 2 - x * a := by ring
  have h2 : (x : Int) * ((a : Int) * (((2 : Int) + (2 ^ 64 - (x : Int) * a % 2 ^ 64)) % 2 ^ 64) % 2 ^ 64) - 1 ≡
      -(((x : Int) * a - 1) ^ 2) [ZMOD 2 ^ 64] := by
    calc _ ≡ (x : Int) * (a * (2 - x * a)) - 1 [ZMOD 2 ^ 64] :=
          (((Int.mod_modEq _ _).trans (h1.mul_left _)).mul_left _).sub_right 1
      _ = _ := by ring
  have hd1 : (2 : Int) ^ min (2 * k) 64 ∣ 2 ^ 64 := pow_dvd_pow 2 (min_le_right _ _)
  have hd2 : (2 : Int) ^ min (2 * k) 64 ∣ ((x : Int) * a - 1) ^ 2 :=
    (pow_dvd_pow 2 (min_le_left _ _)).trans (by rw [pow_mul']; exact pow_dvd_pow_of_dvd h 2)
  have := dvd_sub (hd1.trans (Int.ModEq.dvd h2.symm)) hd2
  rwa [sub_neg_eq_add, add_sub_cancel_right] at this

/-- A step of a `Range<i32>` below 4. -/
theorem next_i32_spec (r : core.ops.range.Range I32) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 r ⦃ (o : Option I32) (r' : core.ops.range.Range I32) =>
      (if r.start.val < r.end.val then o = some r.start ∧ r'.start.val = r.start.val + 1
       else o = none ∧ r'.start = r.start) ∧ r'.end = r.end ⦄ := by
  unfold core.iter.range.IteratorRange.next
  simp only [core.iter.range.StepI32, core.iter.range.IScalarStep]
  simp [liftFun2, liftFun1, core.cmp.impls.PartialOrdI32.lt, core.clone.impls.CloneI32.clone,
    core.iter.range.IScalarStep.forward_checked]
  by_cases h : r.start.val < r.end.val
  · have hm : r.start.val < I32.max := by scalar_tac
    simp only [h, hm, ↓reduceIte, ↓reduceDIte, bind_ok, WP.spec_ok]
    simp [IScalar.ofInt_val_eq]
  · simp only [h, ↓reduceIte, WP.spec_ok]; simp

theorem negmodinv_loop_spec (x : U64) (iter : core.ops.range.Range I32) (inv : U64)
    (hend : iter.end.val = 4) (hs0 : 0 ≤ iter.start.val) (hs4 : iter.start.val ≤ 4)
    (hinv : x.val % 2 = 1 → (2 : Int) ^ min (5 * 2 ^ iter.start.toNat) 64 ∣ (x.val : Int) * inv.val - 1) :
    low.generic.bignum.bignum_negmodinv_loop iter x inv ⦃ r =>
      x.val % 2 = 1 → (2 : Int) ^ 64 ∣ (x.val : Int) * r.val - 1 ⦄ := by
  unfold low.generic.bignum.bignum_negmodinv_loop
  apply loop.spec_decr_nat (fun x' => (4 - x'.1.start.val).toNat)
    (fun x' : core.ops.range.Range I32 × U64 =>
      x'.1.end.val = 4 ∧ 0 ≤ x'.1.start.val ∧ x'.1.start.val ≤ 4 ∧
      (x.val % 2 = 1 → (2 : Int) ^ min (5 * 2 ^ x'.1.start.val.toNat) 64 ∣ (x.val : Int) * x'.2.val - 1))
  · rintro ⟨it, v⟩ ⟨he, hs0, hs4, hv⟩
    simp only at he hs0 hs4 hv
    unfold low.generic.bignum.bignum_negmodinv_loop.body
    step with next_i32_spec it as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h4 : it.start.val = 4 := by
        split at hop
        · simp at hop
        · omega
      simp only [WP.spec_ok]
      rw [h4] at hv
      simpa using hv
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      simp only [lift_eq, bind_ok, WP.spec_ok]
      refine ⟨by rw [hend1, he], by omega, by omega, ?_, by omega⟩
      intro hodd
      have hn := newton_step x.val v.val _ (hv hodd)
      have hk : min (5 * 2 ^ iter1.start.val.toNat) 64 = min (2 * min (5 * 2 ^ it.start.val.toNat) 64) 64 := by
        rw [hst, show (it.start.val + 1).toNat = it.start.val.toNat + 1 by omega, pow_succ]; omega
      have hsz : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [u64_size]
      rw [hk]
      simpa [core.num.U64.wrapping_mul_val_eq, core.num.U64.wrapping_sub_val_eq, hsz] using hn
  · exact ⟨hend, hs0, hs4, hinv⟩

/-- Negating an inverse of `x` modulo `2^64` gives `-x⁻¹`. -/
theorem neg_inverse_final (x v : Nat) (hv : v ≤ 2 ^ 64) (h : (2 : Int) ^ 64 ∣ (x : Int) * v - 1) :
    (x * ((2 ^ 64 - v) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  have h0 : (2 : Int) ^ 64 ≡ 0 [ZMOD 2 ^ 64] := by simp [Int.ModEq]
  have h1 : (x : Int) * (((2 : Int) ^ 64 - v) % 2 ^ 64) + 1 ≡ -((x : Int) * v - 1) [ZMOD 2 ^ 64] := by
    calc _ ≡ (x : Int) * (0 - v) + 1 [ZMOD 2 ^ 64] :=
          (((Int.mod_modEq _ _).trans (h0.sub_right _)).mul_left _).add_right 1
      _ = _ := by ring
  have h2 : (2 : Int) ^ 64 ∣ (x : Int) * (((2 : Int) ^ 64 - v) % 2 ^ 64) + 1 := by
    have := dvd_add (Int.ModEq.dvd h1.symm) (dvd_neg.mpr h)
    rwa [sub_add_cancel] at this
  have e : ((x * ((2 ^ 64 - v) % 2 ^ 64) + 1 : Nat) : Int) = (x : Int) * (((2 : Int) ^ 64 - v) % 2 ^ 64) + 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Int.natCast_mod, Nat.cast_sub hv]; push_cast; rfl
  rw [← e] at h2
  exact_mod_cast h2

/-- `BIGNUM_NEGMODINV_SUBROUTINE_CORRECT`'s statement, as x86_64's axiom
states it, for the one word `PosInt` takes. -/
@[step]
theorem bignum_negmodinv_spec (z x : Slice U64) (hz : z.length = 1) (hx : x.length = 1) :
    low.generic.bignum.bignum_negmodinv z x ⦃ r =>
      r.length = z.length ∧
        (wordsNat x.val % 2 = 1 →
          (wordsNat x.val * wordsNat r.val + 1) % 2 ^ (64 * z.length) = 0) ⦄ := by
  unfold low.generic.bignum.bignum_negmodinv
  step*
  have hsz : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [u64_size]
  have hxv : x.val = [x1] := by
    have hl : x.val.length = 1 := hx
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp hl
    rw [hw, x1_post]; simp [hw]
  have hinv0 : inv.val = (x1.val * 3 % 2 ^ 64) ^^^ 2 := by
    rw [inv_post, UScalar.val_xor, i2_post, core.num.U64.wrapping_mul_val_eq, hsz]; rfl
  step with negmodinv_loop_spec x1 { start := 0#i32, «end» := 4#i32 } inv (by simp) (by simp) (by simp)
    (fun hodd => by rw [hinv0]; simpa using newton_start x1.val hodd) as ⟨inv1, hinv1⟩
  unfold core.num.U64.wrapping_neg
  simp only [bind_ok]
  step as ⟨r, hr⟩
  have hzl : z.val.length = 1 := hz
  obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp hzl
  refine ⟨by rw [hr, Slice.set_length], fun hodd => ?_⟩
  have hodd' : x1.val % 2 = 1 := by simpa [hxv, wordsNat_cons, wordsNat_nil] using hodd
  rw [hxv, hr, Slice.set_val_eq, hw, hz]
  have hneg := neg_inverse_final x1.val inv1.val (by have := inv1.hBounds; simp at this; omega) (hinv1 hodd')
  simp only [show ((0#usize : Usize) : Nat) = 0 from rfl, List.set_cons_zero, wordsNat_cons, wordsNat_nil,
    mul_zero, add_zero, mul_one]
  convert hneg using 4
  show (-inv1.bv).toNat = _
  rw [BitVec.toNat_neg]; rfl

end rind.portable
