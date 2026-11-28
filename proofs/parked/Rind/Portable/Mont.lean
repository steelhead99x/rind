import Rind.Portable.Funs
import Rind.RsaLemmas
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# The portable backend's Montgomery products

`low::generic::mont`'s routines over 64-bit limbs, each against `Nat`
arithmetic on the limbs `wordsNat` reads.
-/

namespace rind.portable

/-! ## Limbs -/

theorem mul_add_limb_bound (a b c d : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64)
    (hd : d < 2 ^ 64) : a * b + c + d < 2 ^ 128 := by
  have : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem from_u128_val (x : U64) : (core.convert.num.FromU128U64.from x).val = x.val := by
  simp only [core.convert.num.FromU128U64.from, UScalar.val, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_trans x.bv.isLt (by norm_num))

@[step]
theorem from_u128_spec (x : U64) : lift (core.convert.num.FromU128U64.from x) ⦃ r => r.val = x.val ⦄ := by
  simp [lift]

@[step]
theorem mul_add_limb_spec (a b c : U64) (d : U128) (hd : d.val < 2 ^ 64) :
    low.generic.limb64.mont.mul_add_limb a b c d ⦃ r =>
      r.val = a.val * b.val + c.val + d.val ⦄ := by
  unfold low.generic.limb64.mont.mul_add_limb
  have hb := mul_add_limb_bound a.val b.val c.val d.val a.hBounds b.hBounds c.hBounds hd
  have hab : a.val * b.val < 2 ^ 128 := by omega
  simp only [lift, bind_ok, WP.spec_ok, core.num.U128.wrapping_add_val_eq,
    core.num.U128.wrapping_mul_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A `u128`'s low limb. -/
theorem cast_u64_val (t : U128) : (UScalar.cast .U64 t).val = t.val % 2 ^ 64 := by
  simp [UScalar.cast_val_eq]

theorem shr_bits_lt (t : U128) : t.val >>> 64 < 2 ^ 64 := by
  have := t.hBounds
  rw [Nat.shiftRight_eq_div_pow]
  simp only [UScalarTy.numBits] at this
  omega

theorem u64_lt (x : U64) : x.val < 2 ^ 64 := x.hBounds

theorem u64_le (x : U64) : x.val ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt x.hBounds

theorem u64_size : U64.size = 2 ^ 64 := by
  simp [U64.size, U64.numBits]

theorem lift_eq {α : Type} (x : α) : lift x = ok x := rfl

/-! ## Lists of limbs -/

theorem wordsNat_take_succ' (l : List U64) (i : Nat) (hi : i < l.length) :
    wordsNat (l.take (i + 1)) = wordsNat (l.take i) + 2 ^ (64 * i) * l[i]!.val := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, wordsNat_append, wordsNat_cons,
    wordsNat_nil, List.length_take, getElem!_pos l i hi, Nat.min_eq_left hi.le]
  ring

theorem take_set_succ' {α : Type} (l : List α) (i : Nat) (v : α) (hi : i < l.length) :
    (l.set i v).take (i + 1) = l.take i ++ [v] := by
  rw [List.take_add_one, List.getElem?_set_self (by simpa using hi), Option.toList_some,
    List.take_set_of_le (by omega)]

theorem drop_set_succ' {α : Type} (l : List α) (i : Nat) (v : α) :
    (l.set i v).drop (i + 1) = l.drop (i + 1) := by
  rw [List.drop_set]; simp

theorem drop_set_lt {α : Type} (l : List α) (i m : Nat) (v : α) (h : i < m) :
    (l.set i v).drop m = l.drop m := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_drop, List.getElem?_set]
  split <;> first | rfl | omega

theorem getElem!_of_drop_eq {α : Type} [Inhabited α] {l l0 : List α} {i : Nat} (h : l.drop i = l0.drop i) :
    l[i]! = l0[i]! := by
  have := congrArg (·[0]!) h
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero] at this
  simpa [List.getElem!_eq_getElem?_getD] using this

/-- One limb of a multiply-accumulate: the low half of `t = u·y + x + c`
lands at limb `i`, and the high half carries. -/
theorem mac_step {X X0 Y c t i xi yi u : Nat} (hinv : X + 2 ^ (64 * i) * c = X0 + u * Y)
    (ht : t = u * yi + xi + c) :
    X + 2 ^ (64 * i) * (t % 2 ^ 64) + 2 ^ (64 * (i + 1)) * (t / 2 ^ 64) =
      X0 + 2 ^ (64 * i) * xi + u * (Y + 2 ^ (64 * i) * yi) := by
  have h := Nat.mod_add_div t (2 ^ 64)
  rw [show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
  zify at *
  linear_combination (2 ^ (64 * i) : Int) * h + hinv + (2 ^ (64 * i) : Int) * ht

/-! ## `mul_add` -/

theorem mul_add_loop_spec (u : U64) (y x0 : Slice U64) (hy : y.length = x0.length)
    (iter : core.ops.range.Range Usize) (x : Slice U64) (carry : U128)
    (hend : iter.end.val = x0.length) (hi : iter.start.val ≤ x0.length) (hxl : x.length = x0.length)
    (hc : carry.val < 2 ^ 64) (hdrop : x.val.drop iter.start.val = x0.val.drop iter.start.val)
    (hinv : wordsNat (x.val.take iter.start.val) + 2 ^ (64 * iter.start.val) * carry.val =
      wordsNat (x0.val.take iter.start.val) + u.val * wordsNat (y.val.take iter.start.val)) :
    low.generic.limb64.mont.mul_add_loop iter x u y carry ⦃ r =>
      r.2.length = x0.length ∧ r.1.val < 2 ^ 64 ∧
      wordsNat r.2.val + 2 ^ (64 * x0.length) * r.1.val = wordsNat x0.val + u.val * wordsNat y.val ⦄ := by
  unfold low.generic.limb64.mont.mul_add_loop
  apply loop.spec_decr_nat (fun x => x0.length - x.1.start.val)
    (fun x : core.ops.range.Range Usize × Slice U64 × U128 =>
      x.1.end.val = x0.length ∧ x.1.start.val ≤ x0.length ∧ x.2.1.length = x0.length ∧
      x.2.2.val < 2 ^ 64 ∧ x.2.1.val.drop x.1.start.val = x0.val.drop x.1.start.val ∧
      wordsNat (x.2.1.val.take x.1.start.val) + 2 ^ (64 * x.1.start.val) * x.2.2.val =
        wordsNat (x0.val.take x.1.start.val) + u.val * wordsNat (y.val.take x.1.start.val))
  · rintro ⟨it, v, c⟩ ⟨he, hs, hvl, hc, hd, hv⟩
    simp only at he hs hvl hc hd hv
    unfold low.generic.limb64.mont.mul_add_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = x0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hvl' : v.val.length = x0.length := hvl
      have hyl : y.val.length = x0.length := hy
      have hx0l : x0.val.length = x0.length := rfl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨hvl, hc, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hvL : v.length = v.val.length := rfl
      have hyL : y.length = y.val.length := rfl
      have hx0L : x0.length = x0.val.length := rfl
      step as ⟨yi, hyi⟩
      step as ⟨xi, hxi⟩
      step with mul_add_limb_spec u yi xi c hc as ⟨t, ht⟩
      step as ⟨w, hw⟩
      step as ⟨s, hs⟩
      step as ⟨c1, hc1, _⟩
      have hxi0 : xi = x0.val[it.start.val]! := by
        rw [hxi, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      have hsv : s.val = v.val.set it.start.val (UScalar.cast .U64 t) := by rw [hs, hw]; simp
      have hc1v : c1.val = t.val / 2 ^ 64 := by rw [hc1]; simp [Nat.shiftRight_eq_div_pow]
      have htb : t.val < 2 ^ 128 := by
        rw [ht]; exact mul_add_limb_bound _ _ _ _ u.hBounds yi.hBounds xi.hBounds hc
      refine ⟨by rw [hend1, he], by scalar_tac, by rw [hs]; simp at hvl ⊢; omega,
        by rw [hc1v]; omega, ?_, ?_⟩
      · rw [hst, hsv, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < v.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < x0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hsv, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), cast_u64_val, hc1v,
          wordsNat_take_succ' _ _ (by omega), wordsNat_take_succ' _ _ (by omega)]
        have := mac_step (X := wordsNat (v.val.take it.start.val)) hv (ht.trans (by rw [hyi, hxi0]))
        rw [← getElem!_pos] at this
        exact ⟨by simpa using this, by omega⟩
  · exact ⟨hend, hi, hxl, hc, hdrop, hinv⟩

/-- `mul_add`: `x + u·y` over `x`'s limbs, the carry out of the top returned. -/
@[step]
theorem mul_add_spec (x y : Slice U64) (u : U64) (hy : y.length = x.length) :
    low.generic.limb64.mont.mul_add x y u ⦃ r =>
      r.2.length = x.length ∧ r.1.val < 2 ^ 64 ∧
      wordsNat r.2.val + 2 ^ (64 * x.length) * r.1.val = wordsNat x.val + u.val * wordsNat y.val ⦄ := by
  unfold low.generic.limb64.mont.mul_add
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = y.val := by
    rw [hy1]; simp only [Slice.length] at hy; simp [hy]
  have hy1l : y1.length = x.length := by simp [Slice.length, hy1v]; exact hy
  have := mul_add_loop_spec u y1 x hy1l { start := 0#usize, «end» := x.len } x 0#u128 (by simp) (by simp) rfl
    (by simp) rfl (by simp [wordsNat_nil])
  rw [hy1v] at this
  exact this

/-! ## Subtraction with borrow -/

/-- One limb of a subtraction with borrow, as two `overflowing_sub`s. -/
theorem sub_step (xi yi bw diff0 diff1 : Nat) (b1 b2 : Bool) (hxi : xi < 2 ^ 64) (hyi : yi < 2 ^ 64)
    (hbw : bw ≤ 1)
    (h1 : if xi < yi then diff0 + yi = xi + 2 ^ 64 ∧ b1 = true else diff0 = xi - yi ∧ b1 = false)
    (h2 : if diff0 < bw then diff1 + bw = diff0 + 2 ^ 64 ∧ b2 = true else diff1 = diff0 - bw ∧ b2 = false) :
    (xi : Int) - yi - bw = diff1 - 2 ^ 64 * (b1 || b2).toNat := by
  split_ifs at h1 h2 <;> obtain ⟨h1, rfl⟩ := h1 <;> obtain ⟨h2, rfl⟩ := h2 <;> simp <;> omega

theorem from_bool_val (b : Bool) : (core.convert.num.FromU64Bool.from b).val = b.toNat := by
  cases b <;> rfl

/-- The chain's invariant after `i` limbs: the difference of the prefixes is
the limbs written so far, less the borrow out of them. -/
theorem sub_chain_step {X Y D : Int} {bw b : Nat} {xi yi d : Int} (i : Nat)
    (hinv : D - 2 ^ (64 * i) * (bw : Int) = X - Y)
    (hstep : xi - yi - bw = d - 2 ^ 64 * (b : Int)) :
    D + 2 ^ (64 * i) * d - 2 ^ (64 * (i + 1)) * (b : Int) = (X + 2 ^ (64 * i) * xi) - (Y + 2 ^ (64 * i) * yi) := by
  rw [show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
  linear_combination hinv - (2 ^ (64 * i) : Int) * hstep

theorem cmp_lt_limbs_loop_spec (x y : Slice U64) (hy : y.length = x.length)
    (iter : core.ops.range.Range Usize) (borrow : U64)
    (hend : iter.end.val = x.length) (hi : iter.start.val ≤ x.length) (hb : borrow.val ≤ 1)
    (hinv : ∃ D : Nat, D < 2 ^ (64 * iter.start.val) ∧
      (D : Int) - 2 ^ (64 * iter.start.val) * borrow.val =
        wordsNat (x.val.take iter.start.val) - wordsNat (y.val.take iter.start.val)) :
    low.generic.limb64.mont.cmp_lt_limbs_loop iter x y borrow ⦃ r =>
      r.val = if wordsNat x.val < wordsNat y.val then 1 else 0 ⦄ := by
  unfold low.generic.limb64.mont.cmp_lt_limbs_loop
  apply loop.spec_decr_nat (fun x' => x.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × U64 =>
      x'.1.end.val = x.length ∧ x'.1.start.val ≤ x.length ∧ x'.2.val ≤ 1 ∧
      ∃ D : Nat, D < 2 ^ (64 * x'.1.start.val) ∧
        (D : Int) - 2 ^ (64 * x'.1.start.val) * x'.2.val =
          wordsNat (x.val.take x'.1.start.val) - wordsNat (y.val.take x'.1.start.val))
  · rintro ⟨it, bw⟩ ⟨he, hs, hb, D, hD, hv⟩
    simp only at he hs hb hD hv
    unfold low.generic.limb64.mont.cmp_lt_limbs_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = x.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv hD
      have hxl : x.val.length = x.length := rfl
      have hyl : y.val.length = x.length := hy
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hv
      have hD' : (D : Int) < 2 ^ (64 * x.length) := by exact_mod_cast hD
      have hb' : bw.val = 0 ∨ bw.val = 1 := by omega
      rcases hb' with h | h <;> rw [h] at hv ⊢ <;> split_ifs with hlt <;> first | rfl | (exfalso; push_cast at hv; omega)
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hxL : x.length = x.val.length := rfl
      have hyL : y.length = y.val.length := rfl
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
      · rw [hst, wordsNat_take_succ' _ _ (by omega), wordsNat_take_succ' _ _ (by omega)]
        rw [hxi, hyi, ← getElem!_pos, ← getElem!_pos] at hc
        push_cast
        linarith
  · exact ⟨hend, hi, hb, hinv⟩

@[step]
theorem cmp_lt_limbs_spec (x y : Slice U64) (hy : y.length = x.length) :
    low.generic.limb64.mont.cmp_lt_limbs x y ⦃ r =>
      r.val = if wordsNat x.val < wordsNat y.val then 1 else 0 ⦄ := by
  unfold low.generic.limb64.mont.cmp_lt_limbs
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = y.val := by
    rw [hy1]; simp only [Slice.length] at hy; simp [hy]
  have := cmp_lt_limbs_loop_spec x y1 (by simp [Slice.length, hy1v]; exact hy)
    { start := 0#usize, «end» := x.len } 0#u64 (by simp) (by simp) (by simp)
    ⟨0, by simp, by simp [wordsNat_nil]⟩
  rw [hy1v] at this
  exact this

/-! ## `sub_limbs_masked` -/

/-- A mask of all ones or zero. -/
def IsMask (keep : U64) : Prop := keep.val = 0 ∨ keep.val = 2 ^ 64 - 1

theorem and_mask_val (a keep : U64) (h : IsMask keep) :
    (a &&& keep).val = if keep.val = 0 then 0 else a.val := by
  rw [UScalar.val_and]
  rcases h with h | h
  · rw [h]; simp
  · rw [h, ite_eq_right (by norm_num), Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by have := a.hBounds; simpa using this)

/-- What a masked subtraction takes away: `y`, or nothing. -/
def masked (keep : U64) (y : Nat) : Nat := if keep.val = 0 then 0 else y

theorem masked_take_succ (keep : U64) (l : List U64) (i : Nat) (hi : i < l.length) :
    masked keep (wordsNat (l.take (i + 1))) =
      masked keep (wordsNat (l.take i)) + 2 ^ (64 * i) * (if keep.val = 0 then 0 else l[i]!.val) := by
  unfold masked; split <;> simp [wordsNat_take_succ' _ _ hi]

theorem sub_limbs_masked_loop_spec (x0 y : Slice U64) (keep : U64) (hk : IsMask keep)
    (hy : y.length = x0.length) (iter : core.ops.range.Range Usize) (x : Slice U64) (borrow : U64)
    (hend : iter.end.val = x0.length) (hi : iter.start.val ≤ x0.length) (hxl : x.length = x0.length)
    (hb : borrow.val ≤ 1) (hdrop : x.val.drop iter.start.val = x0.val.drop iter.start.val)
    (hinv : (wordsNat (x.val.take iter.start.val) : Int) - 2 ^ (64 * iter.start.val) * borrow.val =
      wordsNat (x0.val.take iter.start.val) - masked keep (wordsNat (y.val.take iter.start.val))) :
    low.generic.limb64.mont.sub_limbs_masked_loop iter x keep y borrow ⦃ r =>
      r.length = x0.length ∧ ∃ b : Nat, b ≤ 1 ∧
        (wordsNat r.val : Int) - 2 ^ (64 * x0.length) * b = wordsNat x0.val - masked keep (wordsNat y.val) ⦄ := by
  unfold low.generic.limb64.mont.sub_limbs_masked_loop
  apply loop.spec_decr_nat (fun x' => x0.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U64 =>
      x'.1.end.val = x0.length ∧ x'.1.start.val ≤ x0.length ∧ x'.2.1.length = x0.length ∧
      x'.2.2.val ≤ 1 ∧ x'.2.1.val.drop x'.1.start.val = x0.val.drop x'.1.start.val ∧
      (wordsNat (x'.2.1.val.take x'.1.start.val) : Int) - 2 ^ (64 * x'.1.start.val) * x'.2.2.val =
        wordsNat (x0.val.take x'.1.start.val) - masked keep (wordsNat (y.val.take x'.1.start.val)))
  · rintro ⟨it, v, bw⟩ ⟨he, hs, hvl, hb, hd, hv⟩
    simp only at he hs hvl hb hd hv
    unfold low.generic.limb64.mont.sub_limbs_masked_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = x0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hvl' : v.val.length = x0.length := hvl
      have hyl : y.val.length = x0.length := hy
      have hx0l : x0.val.length = x0.length := rfl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨hvl, bw.val, hb, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hvL : v.length = v.val.length := rfl
      have hyL : y.length = y.val.length := rfl
      have hx0L : x0.length = x0.val.length := rfl
      step as ⟨xi, hxi⟩
      step as ⟨yi, hyi⟩
      step as ⟨ym, hym⟩
      step as ⟨diff, b1, hd1⟩
      step as ⟨diff1, b2, hd2⟩
      step as ⟨s, hs⟩
      simp only [lift, bind_ok, WP.spec_ok]
      have hymv : ym.val = if keep.val = 0 then 0 else yi.val := by rw [hym]; exact and_mask_val yi keep hk
      have hstep := sub_step xi.val ym.val bw.val diff.val diff1.val b1 b2 xi.hBounds ym.hBounds hb
        (by simpa [u64_size] using hd1) (by simpa [u64_size] using hd2)
      rw [← from_bool_val] at hstep
      have hc := sub_chain_step it.start.val hv hstep
      have hxi0 : xi = x0.val[it.start.val]! := by
        rw [hxi, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      have hsv : s.val = v.val.set it.start.val diff1 := by rw [hs]; simp
      refine ⟨by rw [hend1, he], by omega, by rw [hs]; simp at hvl ⊢; omega,
        by rw [from_bool_val]; cases (b1 || b2) <;> simp, ?_, ?_, by omega⟩
      · rw [hst, hsv, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < v.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < x0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hsv, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), wordsNat_take_succ' _ _ (by omega),
          masked_take_succ _ _ _ (by omega)]
        rw [hymv, hxi0, hyi, ← getElem!_pos] at hc
        push_cast
        split_ifs at hc ⊢ <;> push_cast at hc ⊢ <;> linarith
  · exact ⟨hend, hi, hxl, hb, hdrop, hinv⟩

/-- `sub_limbs_masked`: `x - y` where `keep` is all ones, and `x` where it is
zero, modulo `2^(64n)`. -/
@[step]
theorem sub_limbs_masked_spec (x y : Slice U64) (keep : U64) (hk : IsMask keep) (hy : y.length = x.length) :
    low.generic.limb64.mont.sub_limbs_masked x y keep ⦃ r =>
      r.length = x.length ∧ ∃ b : Nat, b ≤ 1 ∧
        (wordsNat r.val : Int) - 2 ^ (64 * x.length) * b = wordsNat x.val - masked keep (wordsNat y.val) ⦄ := by
  unfold low.generic.limb64.mont.sub_limbs_masked
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = y.val := by
    rw [hy1]; simp only [Slice.length] at hy; simp [hy]
  have := sub_limbs_masked_loop_spec x y1 keep hk (by simp [Slice.length, hy1v]; exact hy)
    { start := 0#usize, «end» := x.len } x 0#u64 (by simp) (by simp) rfl (by simp) rfl
    (by simp [wordsNat_nil, masked])
  rw [hy1v] at this
  exact this

/-- A masked subtraction whose difference is not negative leaves it, and no
borrow. -/
theorem masked_sub_exact {r X S n : Nat} {b : Nat} (hb : b ≤ 1) (hr : r < 2 ^ n) (hS : S ≤ X)
    (h : (r : Int) - 2 ^ n * b = X - S) : r = X - S := by
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · push_cast at h; omega
  · exfalso
    have : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by push_cast; rfl
    push_cast at h; omega

/-! ## `add_shift`, CIOS's reduction step -/

/-- One limb of `add_shift`: the low half of `s = u·m_j + t_j + c` lands a
limb down, at `j - 1`, and the high half carries. -/
theorem shift_step {W T M c s j tj mj u L : Nat} (hj : 1 ≤ j)
    (hinv : 2 ^ 64 * W + 2 ^ (64 * j) * c + L = T + u * M) (hs : s = u * mj + tj + c) :
    2 ^ 64 * (W + 2 ^ (64 * (j - 1)) * (s % 2 ^ 64)) + 2 ^ (64 * (j + 1)) * (s / 2 ^ 64) + L =
      T + 2 ^ (64 * j) * tj + u * (M + 2 ^ (64 * j) * mj) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := Nat.mod_add_div s (2 ^ 64)
  simp only [Nat.add_sub_cancel] at *
  rw [show 64 * (k + 1 + 1) = 64 * k + 64 + 64 by ring, show 64 * (k + 1) = 64 * k + 64 by ring,
    pow_add, pow_add] at *
  zify at *
  linear_combination hinv + (2 ^ (64 * k) * 2 ^ 64 : Int) * h + (2 ^ (64 * k) * 2 ^ 64 : Int) * hs

theorem add_shift_loop_spec (t0 m : Slice U64) (u : U64) (low0 : Nat) (hm : m.length ≤ t0.length)
    (iter : core.ops.range.Range Usize) (t : Slice U64) (carry : U64)
    (hend : iter.end.val = m.length) (h1 : 1 ≤ iter.start.val) (hi : iter.start.val ≤ m.length)
    (htl : t.length = t0.length) (hdrop : t.val.drop iter.start.val = t0.val.drop iter.start.val)
    (hinv : 2 ^ 64 * wordsNat (t.val.take (iter.start.val - 1)) + 2 ^ (64 * iter.start.val) * carry.val + low0 =
      wordsNat (t0.val.take iter.start.val) + u.val * wordsNat (m.val.take iter.start.val)) :
    low.generic.limb64.mont.add_shift_loop iter t m u carry ⦃ r =>
      r.1.length = t0.length ∧ r.1.val.drop m.length = t0.val.drop m.length ∧
      2 ^ 64 * wordsNat (r.1.val.take (m.length - 1)) + 2 ^ (64 * m.length) * r.2.val + low0 =
        wordsNat (t0.val.take m.length) + u.val * wordsNat m.val ⦄ := by
  unfold low.generic.limb64.mont.add_shift_loop
  apply loop.spec_decr_nat (fun x' => m.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U64 =>
      x'.1.end.val = m.length ∧ 1 ≤ x'.1.start.val ∧ x'.1.start.val ≤ m.length ∧
      x'.2.1.length = t0.length ∧ x'.2.1.val.drop x'.1.start.val = t0.val.drop x'.1.start.val ∧
      2 ^ 64 * wordsNat (x'.2.1.val.take (x'.1.start.val - 1)) + 2 ^ (64 * x'.1.start.val) * x'.2.2.val + low0 =
        wordsNat (t0.val.take x'.1.start.val) + u.val * wordsNat (m.val.take x'.1.start.val))
  · rintro ⟨it, v, c⟩ ⟨he, h1, hs, hvl, hd, hv⟩
    simp only at he h1 hs hvl hd hv
    unfold low.generic.limb64.mont.add_shift_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = m.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv hd
      have hml : m.val.length = m.length := rfl
      rw [List.take_of_length_le (l := m.val) (by omega)] at hv
      exact ⟨hvl, hd, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hvL : v.length = v.val.length := rfl
      have hmL : m.length = m.val.length := rfl
      have ht0L : t0.length = t0.val.length := rfl
      step as ⟨mi, hmi⟩
      step as ⟨ti, hti⟩
      step as ⟨cw, hcw⟩
      step with mul_add_limb_spec u mi ti cw (by rw [hcw]; exact c.hBounds) as ⟨s, hsv⟩
      step as ⟨k, hk⟩
      step as ⟨w, hw⟩
      step as ⟨v1, hv1⟩
      step as ⟨sh, hsh, _⟩
      step as ⟨c1, hc1⟩
      have hsb : s.val < 2 ^ 128 := by
        rw [hsv]; exact mul_add_limb_bound _ _ _ _ u.hBounds mi.hBounds ti.hBounds
          (by rw [hcw]; exact c.hBounds)
      have hti0 : ti = t0.val[it.start.val]! := by
        rw [hti, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      have hkv : k.val = it.start.val - 1 := by scalar_tac
      have hv1v : v1.val = v.val.set (it.start.val - 1) (UScalar.cast .U64 s) := by rw [hv1, hw, ← hkv]; simp
      have hshv : sh.val = s.val / 2 ^ 64 := by rw [hsh]; simp [Nat.shiftRight_eq_div_pow]
      refine ⟨by rw [hend1, he], by omega, by omega, by rw [hv1]; simp at hvl ⊢; omega, ?_, ?_, by omega⟩
      · rw [hst, hv1v, drop_set_lt _ _ _ _ (by omega)]
        rw [List.drop_eq_getElem_cons (show it.start.val < v.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < t0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hv1v, show it.start.val + 1 - 1 = (it.start.val - 1) + 1 by omega,
          take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), cast_u64_val,
          wordsNat_take_succ' _ _ (by omega), wordsNat_take_succ' (l := m.val) _ (by omega)]
        have hcv : c1.val = s.val / 2 ^ 64 := by
          rw [hc1, cast_u64_val, hshv, Nat.mod_eq_of_lt (by omega)]
        rw [hcv]
        have := shift_step (by omega : 1 ≤ it.start.val) hv
          (hsv.trans (by rw [hcw, hmi, hti0, ← getElem!_pos]))
        exact this
  · exact ⟨hend, h1, hi, htl, hdrop, hinv⟩

/-- `add_shift`: `t[..k - 1] := (t[..k] + u m) / 2^64` for `m` of `k`
limbs, returning the carry out of the top, where the low limb dropped is
`(u m[0] + t[0]) mod 2^64`. -/
@[step]
theorem add_shift_spec (t m : Slice U64) (u : U64) (hk1 : 1 ≤ m.length) (hm : m.length ≤ t.length) :
    low.generic.limb64.mont.add_shift t m u ⦃ r =>
      r.1.val < 2 ^ 64 ∧ r.2.length = t.length ∧ r.2.val.drop m.length = t.val.drop m.length ∧
      2 ^ 64 * wordsNat (r.2.val.take (m.length - 1)) + 2 ^ (64 * m.length) * r.1.val +
        (u.val * m.val[0]!.val + t.val[0]!.val) % 2 ^ 64 =
        wordsNat (t.val.take m.length) + u.val * wordsNat m.val ⦄ := by
  unfold low.generic.limb64.mont.add_shift
  have hmL : m.val.length = m.length := rfl
  have htL : t.val.length = t.length := rfl
  step as ⟨mi, hmi⟩
  step as ⟨ti, hti⟩
  step with mul_add_limb_spec u mi ti 0#u128 (by simp) as ⟨s, hsv⟩
  simp only [lift, bind_ok]
  step as ⟨t1, ht1⟩
  step as ⟨sh, hsh, _⟩
  have hsb : s.val < 2 ^ 128 := by
    rw [hsv]; exact mul_add_limb_bound _ _ _ _ u.hBounds mi.hBounds ti.hBounds (by simp)
  have hshv : sh.val = s.val / 2 ^ 64 := by rw [hsh]; simp [Nat.shiftRight_eq_div_pow]
  have hcv : (UScalar.cast .U64 sh).val = s.val / 2 ^ 64 := by
    rw [cast_u64_val, hshv, Nat.mod_eq_of_lt (by omega)]
  have hmi' : mi = m.val[0]! := by rw [hmi, ← getElem!_pos]
  have hti' : ti = t.val[0]! := by rw [hti, ← getElem!_pos]
  have ht1v : t1.val = t.val.set 0 (UScalar.cast .U64 s) := by rw [ht1]; simp
  step with add_shift_loop_spec t m u (s.val % 2 ^ 64) hm { start := 1#usize, «end» := m.len } t1
    (UScalar.cast .U64 sh) (by simp) (by simp) (by simp; omega) (by simp only [Slice.length]; rw [ht1v]; simp)
    (by rw [ht1v]; simpa using drop_set_succ' t.val 0 (UScalar.cast .U64 s))
    (by
      rw [show (1#usize).val = 1 by simp, Nat.sub_self, List.take_zero, wordsNat_nil, hcv,
        wordsNat_take_succ' (l := t.val) 0 (by omega), wordsNat_take_succ' (l := m.val) 0 (by omega),
        List.take_zero, List.take_zero, wordsNat_nil, ← hmi', ← hti']
      have := Nat.mod_add_div s.val (2 ^ 64)
      rw [show 64 * 1 = 64 by rfl, show 64 * 0 = 0 by rfl, pow_zero]
      simp only [zero_add, one_mul]
      omega)
    as ⟨t2, carry1, ht2l, ht2d, ht2⟩
  refine ⟨by rw [from_u128_val]; exact u64_lt carry1, ht2l, ht2d, ?_⟩
  rw [from_u128_val, ← hmi', ← hti']
  rw [hsv, add_zero] at ht2
  exact ht2

/-! ## `mul_add2` -/

/-- `mul_add2`'s block of limbs. -/
abbrev Block := Std.Array U64 4#usize

theorem four_val : (4#usize).val = 4 := by simp

theorem block_eq : low.generic.limb64.mont.BLOCK = 4#usize := by
  unfold low.generic.limb64.mont.BLOCK
  simp [core.num.U64.BITS]

/-- `foldlM` of a step that appends one value a call, leaving its state. -/
theorem foldlM_append_spec {α β S : Type} (φ : List β × S → α → Result (List β × S)) (s : S)
    (P : α → β → Prop) (hφ : ∀ acc a, φ (acc, s) a ⦃ r => ∃ y, r = (acc ++ [y], s) ∧ P a y ⦄)
    (l : List α) (acc : List β) :
    l.foldlM φ (acc, s) ⦃ r => ∃ ys, r = (acc ++ ys, s) ∧ List.Forall₂ P l ys ⦄ := by
  induction l generalizing acc with
  | nil => exact (WP.spec_ok (acc, s)).mpr ⟨[], by simp, List.Forall₂.nil⟩
  | cons a l ih =>
    rw [List.foldlM_cons]
    apply WP.spec_bind (hφ acc a)
    rintro r ⟨y, rfl, hy⟩
    apply WP.spec_mono (ih (acc ++ [y]))
    rintro r ⟨ys, rfl, hys⟩
    exact ⟨y :: ys, by simp, List.Forall₂.cons hy hys⟩

/-- `core::array::from_fn` of a closure that leaves its state: element `k`
is what the closure returns for `k`. -/
theorem from_fn_spec {T F : Type} [Inhabited T] (N : Usize) (n : Nat) (hn : N.val = n)
    (inst : core.ops.function.FnMut F Usize T) (f : F) (P : Nat → T → Prop)
    (hcall : ∀ i : Usize, i.val < n → inst.call_mut f i ⦃ r => r.2 = f ∧ P i.val r.1 ⦄) :
    core.array.from_fn N inst f ⦃ a => ∀ k < n, P k a.val[k]! ⦄ := by
  subst hn
  unfold core.array.from_fn
  apply WP.spec_bind (foldlM_append_spec _ f (fun a y => P a.val y) ?_ _ [])
  · rintro r ⟨ys, rfl, hys⟩
    obtain ⟨hl, hget⟩ := List.forall₂_iff_get.mp hys
    simp only [List.length_attach, List.length_range] at hl
    change (if h : ys.length = N.val then ok (Std.Array.from ys h) else fail .panic) ⦃ a => ∀ k < N.val, P k a.val[k]! ⦄
    rw [dite_eq_left hl.symm, WP.spec_ok]
    intro k hk
    have := hget k (by simp; omega) (by omega)
    simpa [getElem!_pos ys k (by omega)] using this
  · rintro acc ⟨i, hi⟩
    have hiN : i < N.val := List.mem_range.mp hi
    dsimp only
    apply WP.spec_bind (hcall _ (by simpa using hiN))
    rintro ⟨y, f'⟩ ⟨hf, hy⟩
    subst hf
    refine (WP.spec_ok _).mpr ⟨y, rfl, ?_⟩
    simpa using hy

theorem closure_spec (u : U64) (y : Std.Array U64 4#usize) (i : Usize) (hi : i.val < 4) :
    low.generic.limb64.mont.mul_add2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU128.call_mut (u, y) i
      ⦃ r => r.2 = (u, y) ∧ r.1.val = u.val * y.val[i.val]!.val ⦄ := by
  unfold low.generic.limb64.mont.mul_add2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU128.call_mut
  simp only [lift, bind_ok]
  step with Array.index_usize_spec y i (by simpa using hi) as ⟨yi, hyi⟩
  have hb : u.val * yi.val < 2 ^ 128 := by
    have := mul_add_limb_bound u.val yi.val 0 0 u.hBounds yi.hBounds (by norm_num) (by norm_num); omega
  simp only [core.num.U128.wrapping_mul_val_eq, from_u128_val, UScalar.size,
    UScalarTy.numBits]
  refine ⟨rfl, ?_⟩
  rw [Nat.mod_eq_of_lt hb, hyi, getElem!_pos _ _ (by simpa using hi)]

/-- The multiple of `v` that limb `k` of `mul_add2`'s second chain adds:
the limb of `y` below `k`, or `prev` at the bottom. -/
def prevAt (prev : U64) (y : List U64) (k : Nat) : Nat := if k = 0 then prev.val else y[k - 1]!.val

theorem closure1_spec (prev : U64) (y : Std.Array U64 4#usize) (v : U64) (i : Usize) (hi : i.val < 4) :
    low.generic.limb64.mont.mul_add2.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU128.call_mut
      (prev, y, v) i ⦃ r => r.2 = (prev, y, v) ∧ r.1.val = v.val * prevAt prev y.val i.val ⦄ := by
  have hcall : low.generic.limb64.mont.mul_add2.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU128.call_mut
      (prev, y, v) i = (do
        let below1 ← if i = 0#usize then ok prev else do
          let i1 ← i - 1#usize
          Array.index_usize y i1
        let i1 ← lift (core.convert.num.FromU128U64.from v)
        let i2 ← lift (core.convert.num.FromU128U64.from below1)
        let i3 ← lift (core.num.U128.wrapping_mul i1 i2)
        ok (i3, ((prev, y, v) : low.generic.limb64.mont.mul_add2.closure_1))) := rfl
  rw [hcall]
  have key : ∀ b : U64, b.val = prevAt prev y.val i.val →
      (do
        let i1 ← lift (core.convert.num.FromU128U64.from v)
        let i2 ← lift (core.convert.num.FromU128U64.from b)
        let i3 ← lift (core.num.U128.wrapping_mul i1 i2)
        ok (i3, ((prev, y, v) : low.generic.limb64.mont.mul_add2.closure_1)))
        ⦃ r => r.2 = (prev, y, v) ∧ r.1.val = v.val * prevAt prev y.val i.val ⦄ := by
    intro b hb
    have hbb : v.val * b.val < 2 ^ 128 := by
      have := mul_add_limb_bound v.val b.val 0 0 v.hBounds b.hBounds (by norm_num) (by norm_num); omega
    simp only [lift, bind_ok, WP.spec_ok, core.num.U128.wrapping_mul_val_eq, from_u128_val, UScalar.size,
      UScalarTy.numBits, true_and]
    rw [Nat.mod_eq_of_lt hbb, hb]
  split
  · rename_i h0
    simp only [bind_ok]
    exact key prev (by simp [prevAt, h0])
  · rename_i h0
    have h0' : i.val ≠ 0 := by intro h; apply h0; scalar_tac
    step as ⟨j, hj⟩
    step with Array.index_usize_spec y j (by simp; omega) as ⟨b, hb⟩
    exact key b (by rw [hb, ← getElem!_pos]; simp [prevAt, h0', hj])

/-- The products of `u` and a block's limbs. -/
theorem pu_spec (u : U64) (y : Std.Array U64 4#usize) :
    core.array.from_fn 4#usize
      low.generic.limb64.mont.mul_add2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU128
      ((u, y) : low.generic.limb64.mont.mul_add2.closure)
      ⦃ a => ∀ k < 4, a.val[k]!.val = u.val * y.val[k]!.val ⦄ := by
  exact from_fn_spec 4#usize 4 four_val
    low.generic.limb64.mont.mul_add2.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU128 (u, y)
    (fun k r => r.val = u.val * y.val[k]!.val)
    (fun i hi => closure_spec u y i hi)

/-- The products of `v` and the limbs a block's second chain adds. -/
theorem pv_spec (prev : U64) (y : Std.Array U64 4#usize) (v : U64) :
    core.array.from_fn 4#usize
      low.generic.limb64.mont.mul_add2.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU128
      ((prev, y, v) : low.generic.limb64.mont.mul_add2.closure_1)
      ⦃ a => ∀ k < 4, a.val[k]!.val = v.val * prevAt prev y.val k ⦄ := by
  exact from_fn_spec 4#usize 4 four_val
    low.generic.limb64.mont.mul_add2.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU128 (prev, y, v)
    (fun k r => r.val = v.val * prevAt prev y.val k)
    (fun i hi => closure1_spec prev y v i hi)

/-- One limb of `mul_add2`: the first chain's sum `s0 = u·y_j + x_j + c0`
passes its low half to the second's, `s1 = v·prev + s0 mod 2^64 + c1`,
whose low half lands at limb `j`. -/
theorem mac2_step {X X0 Y C c0 c1 s0 s1 j xj yj u v P : Nat}
    (hinv : X + 2 ^ (64 * j) * (c0 + c1 + v * P) = X0 + (u + 2 ^ 64 * v) * Y + C)
    (hs0 : s0 = u * yj + xj + c0) (hs1 : s1 = v * P + s0 % 2 ^ 64 + c1) :
    X + 2 ^ (64 * j) * (s1 % 2 ^ 64) + 2 ^ (64 * (j + 1)) * (s0 / 2 ^ 64 + s1 / 2 ^ 64 + v * yj) =
      X0 + 2 ^ (64 * j) * xj + (u + 2 ^ 64 * v) * (Y + 2 ^ (64 * j) * yj) + C := by
  have h0 := Nat.mod_add_div s0 (2 ^ 64)
  have h1 := Nat.mod_add_div s1 (2 ^ 64)
  rw [show 64 * (j + 1) = 64 * j + 64 by ring, pow_add]
  zify at *
  linear_combination hinv + (2 ^ (64 * j) : Int) * (h1 + h0 + hs1 + hs0)

theorem mul_add2_block_loop_spec (u v prev : U64) (y x0 : Std.Array U64 4#usize) (pu pv : Std.Array U128 4#usize)
    (hpu : ∀ k < 4, pu.val[k]!.val = u.val * y.val[k]!.val)
    (hpv : ∀ k < 4, pv.val[k]!.val = v.val * prevAt prev y.val k) (C : Nat)
    (iter : core.ops.range.Range Usize) (c0 c1 : U128) (x : Std.Array U64 4#usize)
    (hend : iter.end.val = 4) (hi : iter.start.val ≤ 4) (hc0 : c0.val < 2 ^ 64) (hc1 : c1.val < 2 ^ 64)
    (hdrop : x.val.drop iter.start.val = x0.val.drop iter.start.val)
    (hinv : wordsNat (x.val.take iter.start.val) +
        2 ^ (64 * iter.start.val) * (c0.val + c1.val + v.val * prevAt prev y.val iter.start.val) =
      wordsNat (x0.val.take iter.start.val) + (u.val + 2 ^ 64 * v.val) * wordsNat (y.val.take iter.start.val) + C) :
    low.generic.limb64.mont.mul_add2_loop0_loop0 iter c0 c1 x pu pv ⦃ r =>
      r.1.val < 2 ^ 64 ∧ r.2.1.val < 2 ^ 64 ∧
      wordsNat r.2.2.val + 2 ^ 256 * (r.1.val + r.2.1.val + v.val * prevAt prev y.val 4) =
        wordsNat x0.val + (u.val + 2 ^ 64 * v.val) * wordsNat y.val + C ⦄ := by
  unfold low.generic.limb64.mont.mul_add2_loop0_loop0
  apply loop.spec_decr_nat (fun x' => 4 - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × U128 × U128 × Std.Array U64 4#usize =>
      x'.1.end.val = 4 ∧ x'.1.start.val ≤ 4 ∧ x'.2.1.val < 2 ^ 64 ∧ x'.2.2.1.val < 2 ^ 64 ∧
      x'.2.2.2.val.drop x'.1.start.val = x0.val.drop x'.1.start.val ∧
      wordsNat (x'.2.2.2.val.take x'.1.start.val) +
          2 ^ (64 * x'.1.start.val) * (x'.2.1.val + x'.2.2.1.val + v.val * prevAt prev y.val x'.1.start.val) =
        wordsNat (x0.val.take x'.1.start.val) +
          (u.val + 2 ^ 64 * v.val) * wordsNat (y.val.take x'.1.start.val) + C)
  · rintro ⟨it, a, b, w⟩ ⟨he, hs, ha, hb, hd, hv⟩
    simp only at he hs ha hb hd hv
    unfold low.generic.limb64.mont.mul_add2_loop0_loop0.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = 4 := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwl : w.val.length = 4 := by simp
      have hyl : y.val.length = 4 := by simp
      have hx0l : x0.val.length = 4 := by simp
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨ha, hb, hv⟩
    | some k =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwl : w.val.length = 4 := by simp
      have hyl : y.val.length = 4 := by simp
      have hx0l : x0.val.length = 4 := by simp
      step with Array.index_usize_spec pu it.start (by simp; omega) as ⟨pk, hpk⟩
      step with Array.index_usize_spec w it.start (by simp; omega) as ⟨xk, hxk⟩
      have hpkv : pk.val = u.val * y.val[it.start.val]!.val := by rw [hpk, ← getElem!_pos]; exact hpu _ hlt
      have hxk0 : xk = x0.val[it.start.val]! := by rw [hxk, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      have hpkb : pk.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
        rw [hpkv]; exact Nat.mul_le_mul (u64_le _) (u64_le _)
      have hs0b : pk.val + xk.val + a.val < 2 ^ 128 := by have := u64_lt xk; omega
      simp only [lift, bind_ok]
      step as ⟨c0', hc0', _⟩
      step with Array.index_usize_spec pv it.start (by simp; omega) as ⟨qk, hqk⟩
      have hqkv : qk.val = v.val * prevAt prev y.val it.start.val := by
        rw [hqk, ← getElem!_pos]; exact hpv _ hlt
      have hqkb : qk.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
        rw [hqkv]; refine Nat.mul_le_mul (u64_le _) ?_
        unfold prevAt; split <;> exact u64_le _
      step with Array.update_spec w it.start _ (by simp; omega) as ⟨w1, hw1⟩
      step as ⟨c1', hc1', _⟩
      set s0 := core.num.U128.wrapping_add (core.num.U128.wrapping_add pk (core.convert.num.FromU128U64.from xk)) a
        with hs0def
      set s1 := core.num.U128.wrapping_add (core.num.U128.wrapping_add qk
        (core.convert.num.FromU128U64.from (UScalar.cast UScalarTy.U64 s0))) b with hs1def
      have hs0v : s0.val = pk.val + xk.val + a.val := by
        rw [hs0def]
        simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hs0m : s0.val % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
      have hs1v : s1.val = qk.val + s0.val % 2 ^ 64 + b.val := by
        rw [hs1def]
        simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, cast_u64_val, UScalar.size,
          UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hc0v : c0'.val = s0.val / 2 ^ 64 := by rw [hc0']; simp [Nat.shiftRight_eq_div_pow]
      have hc1v : c1'.val = s1.val / 2 ^ 64 := by rw [hc1']; simp [Nat.shiftRight_eq_div_pow]
      have hw1v : w1.val = w.val.set it.start.val (UScalar.cast .U64 s1) := by rw [hw1]; simp
      refine ⟨by rw [hend1, he], by omega, by rw [hc0v]; omega, by rw [hc1v]; omega, ?_, ?_, by omega⟩
      · rw [hst, hw1v, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < w.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < x0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · have hP : prevAt prev y.val (it.start.val + 1) = y.val[it.start.val]!.val := by simp [prevAt]
        rw [hst, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), cast_u64_val, hc0v, hc1v, hP,
          wordsNat_take_succ' _ _ (by omega), wordsNat_take_succ' (l := y.val) _ (by omega), ← hxk0]
        have := mac2_step hv (hs0v.trans (by rw [hpkv])) (hs1v.trans (by rw [hqkv]))
        simpa using this
  · exact ⟨hend, hi, hc0, hc1, hdrop, hinv⟩

/-- `mul_add2`'s blocks, flattened back into limbs. -/
def flat (cs : List Block) : List U64 := cs.flatMap (·.val)

theorem flat_append (a b : List Block) : flat (a ++ b) = flat a ++ flat b :=
  List.flatMap_append ..

theorem flat_singleton (a : Block) : flat [a] = a.val := by simp [flat]

theorem flat_length (cs : List Block) : (flat cs).length = 4 * cs.length := by
  induction cs with
  | nil => simp [flat]
  | cons a cs ih =>
    rw [show a :: cs = [a] ++ cs from rfl, flat_append, List.length_append, ih, flat_singleton]
    simp; ring

theorem wordsNat_flat_take_succ (cs : List Block) (b : Nat) (hb : b < cs.length) :
    wordsNat (flat (cs.take (b + 1))) = wordsNat (flat (cs.take b)) + 2 ^ (64 * (4 * b)) * wordsNat (cs[b]'hb).val := by
  rw [List.take_add_one, List.getElem?_eq_getElem hb, Option.toList_some, flat_append, flat_singleton,
    wordsNat_append, flat_length, List.length_take, Nat.min_eq_left hb.le]

theorem flat_ofFn (s : List U64) (k : Nat) (hk : k * 4 ≤ s.length) (f : Fin k → Block)
    (hf : ∀ i, (f i).val = (s.drop (i.val * 4)).take 4) : flat (List.ofFn f) = s.take (k * 4) := by
  induction k with
  | zero => simp [flat]
  | succ k ih =>
    rw [List.ofFn_succ_last, flat_append, ih (by omega) _ (fun i => hf _), flat_singleton, hf,
      show (k + 1) * 4 = k * 4 + 4 by ring, List.take_add]
    simp

@[step]
theorem as_chunks4_spec (s : Slice U64) :
    core.slice.Slice.as_chunks 4#usize s ⦃ p => p.1.length = s.length / 4 ∧ flat p.1.val ++ p.2.val = s.val ⦄ := by
  unfold core.slice.Slice.as_chunks
  simp only [four_val, OfNat.ofNat_ne_zero, ↓reduceIte, WP.spec_ok]
  refine ⟨by simp [Slice.length], ?_⟩
  simp only [Slice.from_val]
  rw [flat_ofFn s.val _ (by simp [Slice.length]; omega) _ (fun i => by simp [Std.Array.from_val])]
  exact List.take_append_drop _ _

@[step]
theorem as_chunks_mut4_spec (s : Slice U64) :
    core.slice.Slice.as_chunks_mut 4#usize s ⦃ p back =>
      p.1.length = s.length / 4 ∧ flat p.1.val ++ p.2.val = s.val ∧
      ∀ c t, (flat c.val ++ t.val).length ≤ Usize.max → (back (c, t)).val = flat c.val ++ t.val ⦄ := by
  unfold core.slice.Slice.as_chunks_mut
  apply WP.spec_bind (as_chunks4_spec s)
  rintro p ⟨hl, hf⟩
  simp only [WP.spec_ok]
  refine ⟨hl, hf, fun c t hct => ?_⟩
  simp only [flat] at hct ⊢
  rw [dite_eq_left hct, Slice.from_val]

theorem mul_add2_tail_loop_spec (u v : U64) (y x0 : Slice U64) (hy : y.length = x0.length) (C : Nat)
    (iter : core.ops.range.Range Usize) (c0 c1 : U128) (prev : U64) (x : Slice U64)
    (hend : iter.end.val = x0.length) (hi : iter.start.val ≤ x0.length) (hxl : x.length = x0.length)
    (hc0 : c0.val < 2 ^ 64) (hc1 : c1.val < 2 ^ 64)
    (hdrop : x.val.drop iter.start.val = x0.val.drop iter.start.val)
    (hinv : wordsNat (x.val.take iter.start.val) + 2 ^ (64 * iter.start.val) * (c0.val + c1.val + v.val * prev.val) =
      wordsNat (x0.val.take iter.start.val) + (u.val + 2 ^ 64 * v.val) * wordsNat (y.val.take iter.start.val) + C) :
    low.generic.limb64.mont.mul_add2_loop1 iter u v c0 c1 prev x y ⦃ r =>
      r.2.2.2.length = x0.length ∧ r.1.val < 2 ^ 64 ∧ r.2.1.val < 2 ^ 64 ∧
      wordsNat r.2.2.2.val + 2 ^ (64 * x0.length) * (r.1.val + r.2.1.val + v.val * r.2.2.1.val) =
        wordsNat x0.val + (u.val + 2 ^ 64 * v.val) * wordsNat y.val + C ⦄ := by
  unfold low.generic.limb64.mont.mul_add2_loop1
  apply loop.spec_decr_nat (fun x' => x0.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × U128 × U128 × U64 × Slice U64 =>
      x'.1.end.val = x0.length ∧ x'.1.start.val ≤ x0.length ∧ x'.2.2.2.2.length = x0.length ∧
      x'.2.1.val < 2 ^ 64 ∧ x'.2.2.1.val < 2 ^ 64 ∧
      x'.2.2.2.2.val.drop x'.1.start.val = x0.val.drop x'.1.start.val ∧
      wordsNat (x'.2.2.2.2.val.take x'.1.start.val) +
          2 ^ (64 * x'.1.start.val) * (x'.2.1.val + x'.2.2.1.val + v.val * x'.2.2.2.1.val) =
        wordsNat (x0.val.take x'.1.start.val) + (u.val + 2 ^ 64 * v.val) * wordsNat (y.val.take x'.1.start.val) + C)
  · rintro ⟨it, a, b, p, w⟩ ⟨he, hs, hwl, ha, hb, hd, hv⟩
    simp only at he hs hwl ha hb hd hv
    unfold low.generic.limb64.mont.mul_add2_loop1.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = x0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwl' : w.val.length = x0.length := hwl
      have hyl : y.val.length = x0.length := hy
      have hx0l : x0.val.length = x0.length := rfl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨hwl, ha, hb, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.length = w.val.length := rfl
      have hyL : y.length = y.val.length := rfl
      have hx0L : x0.length = x0.val.length := rfl
      step as ⟨yi, hyi⟩
      step as ⟨xi, hxi⟩
      step with mul_add_limb_spec u yi xi a ha as ⟨s0, hs0⟩
      step as ⟨c0', hc0', _⟩
      step as ⟨t, ht⟩
      step with mul_add_limb_spec v p t b hb as ⟨s1, hs1⟩
      step as ⟨t1, ht1⟩
      step as ⟨w1, hw1⟩
      step as ⟨c1', hc1', _⟩
      have hxi0 : xi = x0.val[it.start.val]! := by
        rw [hxi, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      have hs0b : s0.val < 2 ^ 128 := by
        rw [hs0]; exact mul_add_limb_bound _ _ _ _ u.hBounds yi.hBounds xi.hBounds ha
      have htv : t.val = s0.val % 2 ^ 64 := by rw [ht, cast_u64_val]
      have hs1b : s1.val < 2 ^ 128 := by
        rw [hs1]; exact mul_add_limb_bound _ _ _ _ v.hBounds p.hBounds t.hBounds hb
      have hc0v : c0'.val = s0.val / 2 ^ 64 := by rw [hc0']; simp [Nat.shiftRight_eq_div_pow]
      have hc1v : c1'.val = s1.val / 2 ^ 64 := by rw [hc1']; simp [Nat.shiftRight_eq_div_pow]
      have hw1v : w1.val = w.val.set it.start.val (UScalar.cast .U64 s1) := by rw [hw1, ht1]; simp
      refine ⟨by rw [hend1, he], by scalar_tac, by rw [hw1]; simp at hwl ⊢; omega,
        by rw [hc0v]; omega, by rw [hc1v]; omega, ?_, ?_, by omega⟩
      · rw [hst, hw1v, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < w.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < x0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), cast_u64_val, hc0v, hc1v,
          wordsNat_take_succ' _ _ (by omega), wordsNat_take_succ' (l := y.val) _ (by omega), ← hxi0]
        have := mac2_step hv hs0 (hs1.trans (by rw [htv]))
        have hyi' : yi = y.val[it.start.val]! := by rw [hyi, ← getElem!_pos]
        rw [hyi'] at this ⊢
        simpa using this
  · exact ⟨hend, hi, hxl, hc0, hc1, hdrop, hinv⟩

theorem mul_add2_blocks_loop_spec (u v : U64) (ys xs0 : Slice Block)
    (hy : ys.length = xs0.length) (c : Nat)
    (iter : core.ops.range.Range Usize) (c0 c1 : U128) (prev : U64) (xs : Slice Block)
    (hend : iter.end.val = xs0.length) (hi : iter.start.val ≤ xs0.length) (hxl : xs.length = xs0.length)
    (hc0 : c0.val < 2 ^ 64) (hc1 : c1.val < 2 ^ 64)
    (hdrop : xs.val.drop iter.start.val = xs0.val.drop iter.start.val)
    (hinv : wordsNat (flat (xs.val.take iter.start.val)) +
        2 ^ (64 * (4 * iter.start.val)) * (c0.val + c1.val + v.val * prev.val) =
      wordsNat (flat (xs0.val.take iter.start.val)) +
        (u.val + 2 ^ 64 * v.val) * wordsNat (flat (ys.val.take iter.start.val)) + c) :
    low.generic.limb64.mont.mul_add2_loop0 iter u v c0 c1 prev xs ys ⦃ r =>
      r.2.2.2.length = xs0.length ∧ r.1.val < 2 ^ 64 ∧ r.2.1.val < 2 ^ 64 ∧
      wordsNat (flat r.2.2.2.val) + 2 ^ (64 * (4 * xs0.length)) * (r.1.val + r.2.1.val + v.val * r.2.2.1.val) =
        wordsNat (flat xs0.val) + (u.val + 2 ^ 64 * v.val) * wordsNat (flat ys.val) + c ⦄ := by
  unfold low.generic.limb64.mont.mul_add2_loop0
  apply loop.spec_decr_nat (fun x' => xs0.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × U128 × U128 × U64 × Slice Block =>
      x'.1.end.val = xs0.length ∧ x'.1.start.val ≤ xs0.length ∧ x'.2.2.2.2.length = xs0.length ∧
      x'.2.1.val < 2 ^ 64 ∧ x'.2.2.1.val < 2 ^ 64 ∧
      x'.2.2.2.2.val.drop x'.1.start.val = xs0.val.drop x'.1.start.val ∧
      wordsNat (flat (x'.2.2.2.2.val.take x'.1.start.val)) +
          2 ^ (64 * (4 * x'.1.start.val)) * (x'.2.1.val + x'.2.2.1.val + v.val * x'.2.2.2.1.val) =
        wordsNat (flat (xs0.val.take x'.1.start.val)) +
          (u.val + 2 ^ 64 * v.val) * wordsNat (flat (ys.val.take x'.1.start.val)) + c)
  · rintro ⟨it, a, b, p, w⟩ ⟨he, hs, hwl, ha, hb, hd, hv⟩
    simp only at he hs hwl ha hb hd hv
    unfold low.generic.limb64.mont.mul_add2_loop0.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = xs0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwl' : w.val.length = xs0.length := hwl
      have hyl : ys.val.length = xs0.length := hy
      have hx0l : xs0.val.length = xs0.length := rfl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨hwl, ha, hb, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.length = w.val.length := rfl
      have hyL : ys.length = ys.val.length := rfl
      have hx0L : xs0.length = xs0.val.length := rfl
      simp only [block_eq]
      step as ⟨x, back, hx, hback⟩
      step as ⟨y, hy'⟩
      step with pu_spec u y as ⟨pu, hpu⟩
      step with pv_spec p y v as ⟨pv, hpv⟩
      step with mul_add2_block_loop_spec u v p y x pu pv hpu hpv (a.val + b.val + v.val * p.val)
        { start := 0#usize, «end» := 4#usize } a b x four_val (by simp) ha hb rfl (by simp [prevAt, wordsNat_nil]) as ⟨c0', c1', x1, hc0', hc1', hx1⟩
      step as ⟨i3, hi3⟩
      step with Array.index_usize_spec y i3 (by simp; scalar_tac) as ⟨prev1, hprev1⟩
      have hbv : (back x1).val = w.val.set it.start.val x1 := by rw [hback]; simp
      have hprev1v : prev1.val = prevAt p y.val 4 := by
        rw [hprev1, ← getElem!_pos]; simp [prevAt, hi3]
      rw [List.drop_eq_getElem_cons (show it.start.val < w.val.length by omega),
        List.drop_eq_getElem_cons (show it.start.val < xs0.val.length by omega)] at hd
      have hx0 : x = xs0.val[it.start.val] := by rw [hx]; exact (List.cons.inj hd).1
      refine ⟨by rw [hend1, he], by omega, ?_, hc0', hc1', ?_, ?_, by omega⟩
      · simp only [Slice.length] at hwl ⊢; rw [hbv, List.length_set]; exact hwl
      · rw [hst, hbv, drop_set_succ']
        exact (List.cons.inj hd).2
      · rw [hst, hbv, take_set_succ' _ _ _ (by omega), flat_append, flat_singleton, wordsNat_append, flat_length,
          List.length_take, Nat.min_eq_left (by omega), wordsNat_flat_take_succ _ _ (by omega),
          wordsNat_flat_take_succ (ys.val) _ (by omega), hprev1v, ← hx0, ← hy',
          show 64 * (4 * (it.start.val + 1)) = 64 * (4 * it.start.val) + 256 by ring, pow_add]
        zify at hv hx1 ⊢
        linear_combination hv + (2 ^ (64 * (4 * it.start.val)) : Int) * hx1
  · exact ⟨hend, hi, hxl, hc0, hc1, hdrop, hinv⟩

/-- `mul_add2`: `x + (u + 2^64 v)·y + c` over `x`'s limbs, as many of `y`'s,
what lands above them returned. -/
@[step]
theorem mul_add2_spec (x y : Slice U64) (u v : U64) (c : U128) (hc : c.val < 2 ^ 64) (hy : x.length ≤ y.length) :
    low.generic.limb64.mont.mul_add2 x y u v c ⦃ r =>
      r.2.length = x.length ∧
      wordsNat r.2.val + 2 ^ (64 * x.length) * r.1.val =
        wordsNat x.val + (u.val + 2 ^ 64 * v.val) * wordsNat (y.val.take x.length) + c.val ⦄ := by
  unfold low.generic.limb64.mont.mul_add2
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = y.val.take x.length := by rw [hy1]; simp
  step as ⟨xs, xr, back, hxsl, hxf, hback⟩
  step as ⟨ys, yr, hysl, hyf⟩
  have hxL : x.length = x.val.length := rfl
  have hyL : y.length = y.val.length := rfl
  have hy1L : y1.val.length = x.length := by rw [hy1v, List.length_take]; omega
  have hxfl := congrArg List.length hxf
  have hyfl := congrArg List.length hyf
  rw [List.length_append, flat_length] at hxfl hyfl
  have hxsL : xs.val.length = x.length / 4 := hxsl
  have hysL : ys.val.length = x.length / 4 := by rw [← hy1L]; exact hysl
  step with mul_add2_blocks_loop_spec u v ys xs (by simp only [Slice.length]; omega) c.val
    { start := 0#usize, «end» := xs.len } c 0#u128 0#u64 xs (by simp) (by simp) rfl hc (by simp) rfl
    (by simp [flat, wordsNat_nil]) as ⟨c0, c1, prev, xs1, hxs1l, hc0, hc1, hxs1⟩
  step with mul_add2_tail_loop_spec u v yr xr (by simp only [Slice.length]; omega) (c0.val + c1.val + v.val * prev.val)
    { start := 0#usize, «end» := xr.len } c0 c1 prev xr (by simp) (by simp) rfl hc0 hc1 rfl
    (by simp [wordsNat_nil]) as ⟨c01, c11, prev1, xr1, hxr1l, hc01, hc11, hxr1⟩
  step as ⟨i3, hi3⟩
  step with mul_add_limb_spec v prev1 i3 c11 hc11 as ⟨r, hr⟩
  have hi3v : i3.val = c01.val := by rw [hi3, cast_u64_val, Nat.mod_eq_of_lt hc01]
  have hlen : (flat xs1.val ++ xr1.val).length = x.length := by
    rw [List.length_append, flat_length]; simp only [Slice.length] at hxs1l hxr1l; omega
  have hbv := hback xs1 xr1 (by rw [hlen]; exact x.property)
  refine ⟨by simp only [Slice.length]; rw [hbv]; exact hlen, ?_⟩
  rw [hbv, wordsNat_append, flat_length, ← hxf, ← hy1v, ← hyf, wordsNat_append, wordsNat_append, flat_length,
    flat_length, hr, hi3v]
  have hxs1L : xs1.val.length = x.length / 4 := by simp only [Slice.length] at hxs1l; omega
  have hxrL : xr.length = x.length - 4 * (x.length / 4) := by simp only [Slice.length]; omega
  rw [hxs1L, hxsL, hysL]
  rw [hxrL] at hxr1
  simp only [Slice.length] at hxs1
  rw [hxsL] at hxs1
  rw [show 64 * x.length = 64 * (4 * (x.length / 4)) + 64 * (x.length - 4 * (x.length / 4)) by omega, pow_add]
  zify at hxs1 hxr1 ⊢
  linear_combination hxs1 + (2 ^ (64 * (4 * (x.length / 4))) : Int) * hxr1

/-! ## `redc` -/

theorem setSlice_eq {α : Type} (s w : List α) (i : Nat) (hw : i + w.length ≤ s.length) :
    s.setSlice! i w = s.take i ++ w ++ s.drop (i + w.length) := by
  simp only [List.setSlice!]
  rw [show min w.length (s.length - i) = w.length by omega, List.take_length]

theorem window_eq {α : Type} (s : List α) (i n : Nat) :
    s = s.take i ++ s.slice i (i + n) ++ s.drop (i + n) := by
  simp only [List.slice, Nat.add_sub_cancel_left, List.append_assoc]
  conv_lhs => rw [← List.take_append_drop i s, ← List.take_append_drop n (s.drop i)]
  rw [List.drop_drop]

/-- Writing `w` over the limbs at `i` adds the difference there. -/
theorem wordsNat_window (s w : List U64) (i : Nat) (hw : i + w.length ≤ s.length) :
    wordsNat (s.setSlice! i w) + 2 ^ (64 * i) * wordsNat (s.slice i (i + w.length)) =
      wordsNat s + 2 ^ (64 * i) * wordsNat w := by
  have hsl : (s.slice i (i + w.length)).length = w.length := by simp [List.slice_length]; omega
  conv_rhs => rw [window_eq s i w.length]
  rw [setSlice_eq s w i hw]
  simp only [wordsNat_append, List.length_append, List.length_take, hsl, Nat.min_eq_left (by omega : i ≤ s.length)]
  ring

theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) (i j : Nat) (x : α) (h : i ≠ j) :
    (l.set i x)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h]

/-- Writing `x` at limb `j` adds the difference there. -/
theorem wordsNat_set (s : List U64) (j : Nat) (x : U64) (hj : j < s.length) :
    wordsNat (s.set j x) + 2 ^ (64 * j) * s[j]!.val = wordsNat s + 2 ^ (64 * j) * x.val := by
  have h := wordsNat_window s [x] j (by simp; omega)
  have h1 : s.setSlice! j [x] = s.set j x := by
    rw [setSlice_eq s [x] j (by simp; omega), List.set_eq_take_append_cons_drop]
    simp [hj]
  have h2 : s.slice j (j + [x].length) = [s[j]!] := by
    simp only [List.slice, List.length_singleton, Nat.add_sub_cancel_left, getElem!_pos s j hj]
    exact List.take_one_drop_eq_of_lt_length hj
  rw [h1, h2] at h
  simpa [wordsNat_cons, wordsNat_nil] using h

theorem take_setSlice {α : Type} (s w : List α) (i c : Nat) (hw : i + w.length ≤ s.length) (hc : c ≤ w.length) :
    (s.setSlice! i w).take (i + c) = s.take i ++ w.take c := by
  have hA : (s.take i).length = i := by simp; omega
  have := List.take_length_add_append (l₁ := s.take i) (l₂ := w ++ s.drop (i + w.length)) c
  rw [hA] at this
  rw [setSlice_eq s w i hw, List.append_assoc, this, List.take_append_of_le_length hc]

theorem drop_setSlice {α : Type} (s w : List α) (i : Nat) (hw : i + w.length = s.length) :
    (s.setSlice! i w).drop i = w := by
  rw [setSlice_eq s w i (by omega), List.append_assoc, List.drop_append_of_le_length (by simp; omega)]
  simp [show i + w.length = s.length from hw]

theorem wordsNat_mod_limb (l : List U64) (h : 1 ≤ l.length) : wordsNat l % 2 ^ 64 = l[0]!.val := by
  obtain ⟨a, l, rfl⟩ : ∃ a l', l = a :: l' := ⟨l.head (by rintro rfl; simp at h), l.tail, by simp⟩
  rw [wordsNat_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (u64_lt a)]
  simp

theorem wordsNat_mod_limbs2 (l : List U64) (h : 2 ≤ l.length) :
    wordsNat l % 2 ^ 128 = l[0]!.val + 2 ^ 64 * l[1]!.val := by
  rw [show (2 : Nat) ^ 128 = 2 ^ (64 * 2) by norm_num, ← wordsNat_take_mod]
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l', l = a :: b :: l' := by
    match l, h with
    | a :: b :: l', _ => exact ⟨a, b, l', rfl⟩
  simp [wordsNat_cons, wordsNat_nil]

/-- A multiple `u = a·n0 mod 2^64` of `m0`, for `n0 = -m0⁻¹`, clears `a`'s
low limb. -/
theorem clear_limb {a n0 m0 : Nat} (hn : (m0 * n0 + 1) % 2 ^ 64 = 0) :
    (a + (a * n0 % 2 ^ 64) * m0) % 2 ^ 64 = 0 := by
  have h : a + (a * n0 % 2 ^ 64) * m0 ≡ a * (m0 * n0 + 1) [MOD 2 ^ 64] := by
    have := ((Nat.mod_modEq (a * n0) (2 ^ 64)).mul_right m0).add_left a
    rw [show a * (m0 * n0 + 1) = a + a * n0 * m0 by ring]; exact this
  unfold Nat.ModEq at h
  rw [h, Nat.mul_mod, hn]; simp

/-- `redc`'s two steps a pass clear two limbs: `u` the low one, and `v` the
next, as the first step's sum leaves it. -/
theorem clear_two {a0 a1 m0 m1 n0 u v : Nat} (hn : (m0 * n0 + 1) % 2 ^ 64 = 0) (hu : u = a0 * n0 % 2 ^ 64)
    (hv : v = ((u * m1 + a1 + (u * m0 + a0) / 2 ^ 64) % 2 ^ 64) * n0 % 2 ^ 64) :
    (a0 + 2 ^ 64 * a1 + (u + 2 ^ 64 * v) * (m0 + 2 ^ 64 * m1)) % 2 ^ 128 = 0 := by
  have hc0 : (u * m0 + a0) % 2 ^ 64 = 0 := by
    have := clear_limb (a := a0) hn; rw [← hu] at this; rw [← this]; ring_nf
  have hc := Nat.mod_add_div (u * m0 + a0) (2 ^ 64)
  rw [hc0, zero_add] at hc
  set c := (u * m0 + a0) / 2 ^ 64
  set nx := u * m1 + a1 + c
  have he0 : (nx + v * m0) % 2 ^ 64 = 0 := by
    have := clear_limb (a := nx) hn
    rw [hv, Nat.mod_mul_mod]; rw [← this]
  have he := Nat.mod_add_div (nx + v * m0) (2 ^ 64)
  rw [he0, zero_add] at he
  set e := (nx + v * m0) / 2 ^ 64
  have : a0 + 2 ^ 64 * a1 + (u + 2 ^ 64 * v) * (m0 + 2 ^ 64 * m1) = 2 ^ 128 * (e + v * m1) := by
    simp only [nx] at he
    zify at hc he ⊢
    linear_combination -hc - (2 ^ 64 : Int) * he
  rw [this, Nat.mul_mod_right]

/-- `redc`'s state after clearing `i` limbs of `t`, from `T`: those limbs
are zero, and `t`, with `top` above limb `i + k`, is `T` plus a multiple of
`M` below `2^(64i)`. -/
def RedcInv (T M k p : Nat) (t : Slice U64) (top : U128) (i : Nat) : Prop :=
  t.length = p + k ∧ i ≤ p ∧ top.val < 2 ^ 64 ∧ wordsNat (t.val.take i) = 0 ∧
    ∃ Q, Q < 2 ^ (64 * i) ∧ wordsNat t.val + 2 ^ (64 * (i + k)) * top.val = T + M * Q

theorem redc_loop0_spec (m : Slice U64) (n0 : U64) (k p : Usize) (T : Nat) (hk : k.val = m.length)
    (hn : (m.val[0]!.val * n0.val + 1) % 2 ^ 64 = 0)
    (t : Slice U64) (top : U128) (i : Usize) (hinv : RedcInv T (wordsNat m.val) k.val p.val t top i.val) :
    low.generic.limb64.mont.redc_loop0 t m n0 k p top i ⦃ r =>
      RedcInv T (wordsNat m.val) k.val p.val r.1 r.2.1 r.2.2.val ⦄ := by
  unfold low.generic.limb64.mont.redc_loop0
  apply loop.spec_decr_nat (fun x => p.val + 1 - x.2.2.val)
    (fun x : Slice U64 × U128 × Usize => RedcInv T (wordsNat m.val) k.val p.val x.1 x.2.1 x.2.2.val)
  · rintro ⟨t, top, i⟩ hI
    dsimp only at hI ⊢
    unfold low.generic.limb64.mont.redc_loop0.body
    have hI' := hI
    obtain ⟨htl, hip, htop, hlow, Q, hQ, hval⟩ := hI'
    have htmax : t.length ≤ Usize.max := t.property
    split
    · rename_i hk2
      step as ⟨i1, hi1⟩
      split
      · rename_i hlt
        have hk2' : 2 ≤ k.val := by scalar_tac
        have hlt' : i.val + 1 < p.val := by scalar_tac
        have htL : t.val.length = p.val + k.val := htl
        have hmL : m.val.length = k.val := hk.symm
        step as ⟨ti, hti⟩
        step as ⟨u, hu⟩
        step as ⟨m0, hm0⟩
        step with mul_add_limb_spec u m0 ti 0#u128 (by simp) as ⟨s0, hs0⟩
        step as ⟨cy, hcy, _⟩
        step as ⟨m1, hm1⟩
        step as ⟨ti1, hti1⟩
        have hs0b : s0.val < 2 ^ 128 := by
          rw [hs0]; exact mul_add_limb_bound _ _ _ _ u.hBounds m0.hBounds ti.hBounds (by norm_num)
        have hcyv : cy.val = s0.val / 2 ^ 64 := by rw [hcy]; simp [Nat.shiftRight_eq_div_pow]
        step with mul_add_limb_spec u m1 ti1 cy (by rw [hcyv]; omega) as ⟨nx, hnx⟩
        step as ⟨nxl, hnxl⟩
        step as ⟨v, hv⟩
        step as ⟨ik, hik⟩
        step as ⟨w, back, hw, hwl, hback⟩
        step with mul_add2_spec w m u v 0#u128 (by simp) (by simp only [Slice.length] at hwl ⊢; omega)
          as ⟨rest, w1, hw1l, hw1⟩
        step as ⟨tk, htk⟩
        simp only [lift, bind_ok]
        step as ⟨t2, ht2⟩
        step as ⟨ik1, hik1⟩
        step as ⟨tk1, htk1⟩
        step as ⟨rh, hrh, _⟩
        step as ⟨sh, hsh, _⟩
        step as ⟨ik2, hik2⟩
        step as ⟨t3, ht3⟩
        step as ⟨top1, htop1, _⟩
        step as ⟨i2, hi2⟩
        set sum := core.num.U128.wrapping_add (core.num.U128.wrapping_add (core.convert.num.FromU128U64.from tk)
          (core.convert.num.FromU128U64.from (UScalar.cast UScalarTy.U64 rest))) top with hsumdef
        set sum1 := core.num.U128.wrapping_add (core.num.U128.wrapping_add (core.convert.num.FromU128U64.from tk1) rh)
          sh with hsum1def
        have hiL : i.val + k.val ≤ t.val.length := by omega
        have hwL : w.val.length = k.val := by simp only [Slice.length] at hwl; omega
        have hw1L : w1.val.length = k.val := by simp only [Slice.length] at hw1l; omega
        have huv : u.val = ti.val * n0.val % 2 ^ 64 := by
          rw [hu]; simp [core.num.U64.wrapping_mul_val_eq, u64_size]
        have hvv : v.val = nx.val % 2 ^ 64 * n0.val % 2 ^ 64 := by
          rw [hv, hnxl]; simp [core.num.U64.wrapping_mul_val_eq, cast_u64_val, u64_size, Nat.mod_mul_mod]
        have hrhv : rh.val = rest.val / 2 ^ 64 := by rw [hrh]; simp [Nat.shiftRight_eq_div_pow]
        have hrestb := rest.hBounds
        simp only [UScalarTy.numBits] at hrestb
        have hsumv : sum.val = tk.val + rest.val % 2 ^ 64 + top.val := by
          rw [hsumdef]
          have := u64_lt tk
          have : rest.val % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
          simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, cast_u64_val, UScalar.size,
            UScalarTy.numBits]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hshv : sh.val = sum.val / 2 ^ 64 := by rw [hsh]; simp [Nat.shiftRight_eq_div_pow]
        have hsum1v : sum1.val = tk1.val + rh.val + sh.val := by
          rw [hsum1def]
          have := u64_lt tk1
          have : rh.val < 2 ^ 64 := by rw [hrhv]; omega
          have : sh.val < 4 := by rw [hshv, hsumv]; have := u64_lt tk; omega
          simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have htop1v : top1.val = sum1.val / 2 ^ 64 := by rw [htop1]; simp [Nat.shiftRight_eq_div_pow]
        have hbv : (back w1).val = t.val.setSlice! i.val w1.val := by rw [hback]; simp [Slice.setSlice!_val]
        have hbL : (back w1).val.length = p.val + k.val := by rw [hbv, List.length_setSlice!]; omega
        have htkb : (back w1).val[i.val + k.val]! = tk := by rw [htk, ← getElem!_pos, hik]
        have htkv : tk = t.val[i.val + k.val]! := by
          rw [← htkb, hbv]
          exact List.getElem!_setSlice!_same _ _ _ _ (Or.inr (by omega))
        have ht2v : t2.val = (back w1).val.set (i.val + k.val) (UScalar.cast .U64 sum) := by
          rw [ht2, ← hik]; simp
        have htk1b : t2.val[i.val + k.val + 1]! = tk1 := by rw [htk1, ← getElem!_pos, hik1, hik]
        have ht3v : t3.val = t2.val.set (i.val + k.val + 1) (UScalar.cast .U64 sum1) := by
          rw [ht3]; simp [hik2, hik]
        have hmk : List.take w.length m.val = m.val := List.take_of_length_le (by simp only [Slice.length]; omega)
        have hw1' : wordsNat w1.val + 2 ^ (64 * k.val) * rest.val =
            wordsNat w.val + (u.val + 2 ^ 64 * v.val) * wordsNat m.val := by
          rw [hmk, show w.length = k.val by simp only [Slice.length]; omega] at hw1; simpa using hw1
        have hW := wordsNat_window t.val w1.val i.val (by omega)
        rw [hw1L, show t.val.slice i.val (i.val + k.val) = w.val by rw [hw, hik], ← hbv] at hW
        have hS2 := wordsNat_set (back w1).val (i.val + k.val) (UScalar.cast .U64 sum) (by omega)
        rw [← ht2v, htkb, cast_u64_val] at hS2
        have ht2L : t2.val.length = p.val + k.val := by rw [ht2v, List.length_set]; exact hbL
        have hS3 := wordsNat_set t2.val (i.val + k.val + 1) (UScalar.cast .U64 sum1) (by omega)
        rw [← ht3v, htk1b, cast_u64_val] at hS3
        have hrmd := Nat.mod_add_div rest.val (2 ^ 64)
        have hsmd := Nat.mod_add_div sum.val (2 ^ 64)
        have hs1md := Nat.mod_add_div sum1.val (2 ^ 64)
        rw [hrhv, hshv] at hsum1v
        have hBi : u.val + 2 ^ 64 * v.val + 1 ≤ 2 ^ 128 := by
          have := u64_lt u; have := u64_lt v; omega
        -- The pass clears limbs `i` and `i + 1`.
        have hclear : wordsNat w1.val % 2 ^ 128 = 0 := by
          have h1 : wordsNat w1.val % 2 ^ 128 = (wordsNat w.val + (u.val + 2 ^ 64 * v.val) * wordsNat m.val) % 2 ^ 128 := by
            rw [← hw1', show 64 * k.val = 128 + 64 * (k.val - 2) by omega, pow_add, mul_assoc,
              Nat.add_mul_mod_self_left]
          have hw0 : w.val[0]! = ti := by
            rw [hw, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩, hti, ← getElem!_pos]; simp
          have hw1v : w.val[1]! = ti1 := by
            rw [hw, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩, hti1, ← getElem!_pos, hi1]
          have hWm : wordsNat w.val ≡ ti.val + 2 ^ 64 * ti1.val [MOD 2 ^ 128] := by
            unfold Nat.ModEq
            rw [wordsNat_mod_limbs2 _ (by omega), hw0, hw1v, Nat.mod_eq_of_lt]
            have := u64_lt ti; have := u64_lt ti1; omega
          have hm0v : m.val[0]! = m0 := by rw [hm0, ← getElem!_pos]
          have hm1v : m.val[1]! = m1 := by rw [hm1, ← getElem!_pos]
          have hMm : wordsNat m.val ≡ m0.val + 2 ^ 64 * m1.val [MOD 2 ^ 128] := by
            unfold Nat.ModEq
            rw [wordsNat_mod_limbs2 _ (by omega), hm0v, hm1v, Nat.mod_eq_of_lt]
            have := u64_lt m0; have := u64_lt m1; omega
          have hsum := hWm.add (hMm.mul_left (u.val + 2 ^ 64 * v.val))
          unfold Nat.ModEq at hsum
          rw [h1, hsum]
          refine clear_two (n0 := n0.val) (by rw [← hm0v]; exact hn) huv ?_
          rw [hvv, hnx, hcyv, hs0]; simp
        refine ⟨⟨?_, by omega, ?_, ?_, Q + 2 ^ (64 * i.val) * (u.val + 2 ^ 64 * v.val), ?_, ?_⟩, by omega⟩
        · simp only [Slice.length]; rw [ht3v, List.length_set]; exact ht2L
        · rw [htop1v]; have := u64_lt tk1; have := u64_lt tk; omega
        · have htake : t3.val.take (i.val + 2) = t.val.take i.val ++ w1.val.take 2 := by
            rw [ht3v, List.take_set_of_le (by omega), ht2v, List.take_set_of_le (by omega), hbv,
              take_setSlice _ _ _ _ (by omega) (by omega)]
          rw [hi2, htake, wordsNat_append, hlow, wordsNat_take_mod, show 64 * 2 = 128 by rfl, hclear]
          simp
        · rw [hi2, show 64 * (i.val + 2) = 64 * i.val + 128 by ring, pow_add]
          calc Q + 2 ^ (64 * i.val) * (u.val + 2 ^ 64 * v.val)
              < 2 ^ (64 * i.val) * (u.val + 2 ^ 64 * v.val + 1) := by rw [Nat.mul_add_one]; omega
            _ ≤ 2 ^ (64 * i.val) * 2 ^ 128 := Nat.mul_le_mul_left _ hBi
        · rw [hi2, htop1v]
          zify at hS3 hS2 hW hw1' hval hs1md hsum1v hrmd hsmd hsumv ⊢
          linear_combination hS3 + hS2 + hW + (2 ^ (64 * i.val) : Int) * hw1' + hval +
            (2 ^ (64 * (i.val + k.val + 1)) : Int) * (hs1md + hsum1v) +
            (2 ^ (64 * (i.val + k.val)) : Int) * (hrmd + hsmd + hsumv)
      · simp only [WP.spec_ok]; exact hI
    · simp only [WP.spec_ok]; exact hI
  · exact hinv

theorem redc_loop1_spec (m : Slice U64) (n0 : U64) (k p : Usize) (T : Nat) (hk : k.val = m.length)
    (hk1 : 1 ≤ k.val) (hn : (m.val[0]!.val * n0.val + 1) % 2 ^ 64 = 0)
    (t : Slice U64) (top : U128) (i : Usize) (hinv : RedcInv T (wordsNat m.val) k.val p.val t top i.val) :
    low.generic.limb64.mont.redc_loop1 t m n0 k p top i ⦃ r =>
      RedcInv T (wordsNat m.val) k.val p.val r.1 r.2 p.val ⦄ := by
  unfold low.generic.limb64.mont.redc_loop1
  apply loop.spec_decr_nat (fun x => p.val - x.2.2.val)
    (fun x : Slice U64 × U128 × Usize => RedcInv T (wordsNat m.val) k.val p.val x.1 x.2.1 x.2.2.val)
  · rintro ⟨t, top, i⟩ hI
    dsimp only at hI ⊢
    unfold low.generic.limb64.mont.redc_loop1.body
    have hI' := hI
    obtain ⟨htl, hip, htop, hlow, Q, hQ, hval⟩ := hI'
    have htmax : t.length ≤ Usize.max := t.property
    split
    · rename_i hlt
      have hlt' : i.val < p.val := by scalar_tac
      have htL : t.val.length = p.val + k.val := htl
      have hmL : m.val.length = k.val := hk.symm
      step as ⟨ti, hti⟩
      step as ⟨u, hu⟩
      step as ⟨ik, hik⟩
      step as ⟨w, back, hw, hwl, hback⟩
      step with mul_add_spec w m u (by simp only [Slice.length] at hwl ⊢; omega) as ⟨cy, w1, hw1l, hcy, hw1⟩
      step as ⟨tk, htk⟩
      simp only [lift, bind_ok]
      step as ⟨t2, ht2⟩
      step as ⟨top1, htop1, _⟩
      step as ⟨i2, hi2⟩
      set sum := core.num.U128.wrapping_add (core.num.U128.wrapping_add (core.convert.num.FromU128U64.from tk) cy)
        top with hsumdef
      have hwL : w.val.length = k.val := by simp only [Slice.length] at hwl; omega
      have hw1L : w1.val.length = k.val := by simp only [Slice.length] at hw1l; omega
      have huv : u.val = ti.val * n0.val % 2 ^ 64 := by
        rw [hu]; simp [core.num.U64.wrapping_mul_val_eq, u64_size]
      have hsumv : sum.val = tk.val + cy.val + top.val := by
        rw [hsumdef]
        have := u64_lt tk
        simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have htop1v : top1.val = sum.val / 2 ^ 64 := by rw [htop1]; simp [Nat.shiftRight_eq_div_pow]
      have hbv : (back w1).val = t.val.setSlice! i.val w1.val := by rw [hback]; simp [Slice.setSlice!_val]
      have hbL : (back w1).val.length = p.val + k.val := by rw [hbv, List.length_setSlice!]; omega
      have htkb : (back w1).val[i.val + k.val]! = tk := by rw [htk, ← getElem!_pos, hik]
      have ht2v : t2.val = (back w1).val.set (i.val + k.val) (UScalar.cast .U64 sum) := by
        rw [ht2]; simp [hik]
      have hw1' : wordsNat w1.val + 2 ^ (64 * k.val) * cy.val = wordsNat w.val + u.val * wordsNat m.val := by
        rw [show w.length = k.val by simp only [Slice.length]; omega] at hw1; exact hw1
      have hW := wordsNat_window t.val w1.val i.val (by omega)
      rw [hw1L, show t.val.slice i.val (i.val + k.val) = w.val by rw [hw, hik], ← hbv] at hW
      have hS := wordsNat_set (back w1).val (i.val + k.val) (UScalar.cast .U64 sum) (by omega)
      rw [← ht2v, htkb, cast_u64_val] at hS
      have hsmd := Nat.mod_add_div sum.val (2 ^ 64)
      -- The step clears limb `i`.
      have hclear : wordsNat w1.val % 2 ^ 64 = 0 := by
        have h1 : wordsNat w1.val % 2 ^ 64 = (wordsNat w.val + u.val * wordsNat m.val) % 2 ^ 64 := by
          rw [← hw1', show 64 * k.val = 64 + 64 * (k.val - 1) by omega, pow_add, mul_assoc,
            Nat.add_mul_mod_self_left]
        have hw0 : w.val[0]! = ti := by
          rw [hw, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩, hti, ← getElem!_pos]; simp
        have hWm : wordsNat w.val ≡ ti.val [MOD 2 ^ 64] := by
          unfold Nat.ModEq; rw [wordsNat_mod_limb _ (by omega), hw0, Nat.mod_eq_of_lt (u64_lt ti)]
        have hMm : wordsNat m.val ≡ m.val[0]!.val [MOD 2 ^ 64] := by
          unfold Nat.ModEq; rw [wordsNat_mod_limb _ (by omega), Nat.mod_eq_of_lt (u64_lt _)]
        have hsum := hWm.add (hMm.mul_left u.val)
        unfold Nat.ModEq at hsum
        rw [h1, hsum, huv]
        exact clear_limb hn
      refine ⟨⟨?_, by omega, ?_, ?_, Q + 2 ^ (64 * i.val) * u.val, ?_, ?_⟩, by omega⟩
      · simp only [Slice.length]; rw [ht2v, List.length_set]; exact hbL
      · rw [htop1v, hsumv]; have := u64_lt tk; omega
      · have htake : t2.val.take (i.val + 1) = t.val.take i.val ++ w1.val.take 1 := by
          rw [ht2v, List.take_set_of_le (by omega), hbv, take_setSlice _ _ _ _ (by omega) (by omega)]
        rw [hi2, htake, wordsNat_append, hlow, wordsNat_take_mod, show 64 * 1 = 64 by rfl, hclear]
        simp
      · rw [hi2, show 64 * (i.val + 1) = 64 * i.val + 64 by ring, pow_add]
        calc Q + 2 ^ (64 * i.val) * u.val
            < 2 ^ (64 * i.val) * (u.val + 1) := by rw [Nat.mul_add_one]; omega
          _ ≤ 2 ^ (64 * i.val) * 2 ^ 64 := Nat.mul_le_mul_left _ (u64_lt u)
      · rw [hi2, htop1v]
        zify at hS hW hw1' hval hsmd hsumv ⊢
        linear_combination hS + hW + (2 ^ (64 * i.val) : Int) * hw1' + hval +
          (2 ^ (64 * (i.val + k.val)) : Int) * (hsmd + hsumv)
    · rename_i hge
      have : i.val = p.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [this] at hI; exact hI
  · exact hinv

/-- `0 - b` for a bit `b`: no limb, or every one. -/
theorem neg_bit_val (b : U64) (hb : b.val ≤ 1) :
    (core.num.U64.wrapping_sub 0#u64 b).val = if b.val = 0 then 0 else 2 ^ 64 - 1 := by
  rcases (show b.val = 0 ∨ b.val = 1 by omega) with h | h <;> simp [core.num.U64.wrapping_sub_val_eq, u64_size, h]

theorem neg_bit_mask (b : U64) (hb : b.val ≤ 1) : IsMask (core.num.U64.wrapping_sub 0#u64 b) := by
  unfold IsMask; rw [neg_bit_val b hb]; split <;> simp

theorem or_not_val (t c : U64) (ht : t.val ≤ 1) (hc : c.val ≤ 1) :
    (t ||| (c ^^^ 1#u64)).val = if t.val = 0 ∧ c.val = 1 then 0 else 1 := by
  rw [UScalar.val_or, UScalar.val_xor, show (1#u64).val = 1 by simp]
  rcases (show t.val = 0 ∨ t.val = 1 by omega) with h1 | h1 <;>
    rcases (show c.val = 0 ∨ c.val = 1 by omega) with h2 | h2 <;> simp [h1, h2]

/-- `redc`: for `t` below `2^(64p)·m`, `p` limbs beyond the odd `m`'s `k`,
the `k` limbs from `p` are `t·2^(-64p)` modulo `m`, the inverse taken modulo `m`. -/
@[step]
theorem redc_spec (t m : Slice U64) (n0 : U64) (hk1 : 1 ≤ m.length) (hkt : m.length ≤ t.length)
    (hn0 : (wordsNat m.val * n0.val + 1) % 2 ^ 64 = 0)
    (hT : wordsNat t.val < 2 ^ (64 * (t.length - m.length)) * wordsNat m.val) :
    low.generic.limb64.mont.redc t m n0 ⦃ r =>
      r.length = t.length ∧ wordsNat (r.val.drop (t.length - m.length)) < wordsNat m.val ∧
      wordsNat (r.val.drop (t.length - m.length)) * 2 ^ (64 * (t.length - m.length)) % wordsNat m.val =
        wordsNat t.val % wordsNat m.val ⦄ := by
  unfold low.generic.limb64.mont.redc
  have hmL : m.val.length = m.length := rfl
  have htL : t.val.length = t.length := rfl
  have hn : (m.val[0]!.val * n0.val + 1) % 2 ^ 64 = 0 := by
    rw [← wordsNat_mod_limb _ (by omega), Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    exact hn0
  step as ⟨pp, hpp⟩
  have hppv : pp.val = t.length - m.length := by scalar_tac
  set p := t.length - m.length with hpdef
  set k := m.length with hkdef
  set M := wordsNat m.val
  set T := wordsNat t.val
  step with redc_loop0_spec m n0 m.len pp T (by simp) hn t 0#u128 0#usize
    ⟨by simp [Slice.length] at hppv ⊢; omega, by simp, by simp, by simp [wordsNat_nil], 0, by simp, by simp [T]⟩
    as ⟨t1, top, i1, hI1⟩
  step with redc_loop1_spec m n0 m.len pp T (by simp) (by simp; omega) hn t1 top i1 hI1 as ⟨t2, top1, hI2⟩
  obtain ⟨ht2l, -, htop, hlow, Q, hQ, hval⟩ := hI2
  simp only [Slice.len_val] at ht2l hval
  rw [hppv] at ht2l hlow hQ hval
  have ht2L : t2.val.length = p + k := ht2l
  step as ⟨r, back, hr, hrl, hback⟩
  have hrL : r.length = k := by simp only [Slice.length] at hrl ⊢; omega
  step with cmp_lt_limbs_spec r m (by omega) as ⟨below, hbelow⟩
  -- `t2` is `R` above `p` zero limbs, with `top` above it.
  have hR : wordsNat t2.val = 2 ^ (64 * p) * wordsNat r.val := by
    rw [wordsNat_take_drop t2.val p, hlow, List.length_take, Nat.min_eq_left (by omega), hr, hppv]
    simp
  set R := wordsNat r.val
  have hMk : M < 2 ^ (64 * k) := wordsNat_lt' m.val
  have hX : 2 ^ (64 * p) * (R + 2 ^ (64 * k) * top1.val) = T + M * Q := by
    rw [← hval, hR, show 64 * (p + k) = 64 * p + 64 * k by ring, pow_add]; ring
  have hXlt : R + 2 ^ (64 * k) * top1.val < 2 * M := by
    have h1 : M * Q < M * 2 ^ (64 * p) := Nat.mul_lt_mul_of_pos_left hQ (by
      rcases Nat.eq_zero_or_pos M with h | h
      · rw [h, mul_zero] at hT; omega
      · exact h)
    have h2 : 2 ^ (64 * p) * (R + 2 ^ (64 * k) * top1.val) < 2 ^ (64 * p) * (2 * M) := by
      rw [hX]; nlinarith
    exact Nat.lt_of_mul_lt_mul_left h2
  have htop1 : top1.val ≤ 1 := by
    by_contra h
    have : 2 ^ (64 * k) * 2 ≤ 2 ^ (64 * k) * top1.val := Nat.mul_le_mul_left _ (by omega)
    omega
  have hbel : below.val ≤ 1 := by rw [hbelow]; split <;> simp
  have hcast : (UScalar.cast .U64 top1).val = top1.val := by rw [cast_u64_val, Nat.mod_eq_of_lt (by omega)]
  have hbit : (UScalar.cast .U64 top1 ||| (below ^^^ 1#u64)).val ≤ 1 := by
    rw [or_not_val _ _ (by omega) hbel]; split <;> simp
  simp only [lift, bind_ok]
  step with sub_limbs_masked_spec r m _ (neg_bit_mask _ hbit) (by omega) as ⟨r1, hr1l, b, hb, hr1⟩
  have hr1L : r1.val.length = k := by simp only [Slice.length] at hr1l hrL; omega
  have hdrop : (back r1).val.drop p = r1.val := by
    rw [hback, hppv]; exact drop_setSlice _ _ _ (by omega)
  have hmasked : masked (core.num.U64.wrapping_sub 0#u64 (UScalar.cast .U64 top1 ||| (below ^^^ 1#u64))) M =
      if top1.val = 0 ∧ below.val = 1 then 0 else M := by
    unfold masked
    rw [neg_bit_val _ hbit, or_not_val _ _ (by omega) hbel, hcast]
    by_cases hc : top1.val = 0 ∧ below.val = 1 <;> simp [hc]
  rw [hmasked, hrL] at hr1
  have hr1lt : wordsNat r1.val < 2 ^ (64 * k) := by have := wordsNat_lt' r1.val; rwa [hr1L] at this
  have hRlt : R < 2 ^ (64 * k) := by have := wordsNat_lt' r.val; simp only [Slice.length] at hrL; rwa [hrL] at this
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hT; omega
    · exact h
  have hR1 : wordsNat r1.val = (R + 2 ^ (64 * k) * top1.val) % M := by
    rw [show (2 : Int) ^ (64 * k) = ((2 ^ (64 * k) : Nat) : Int) by push_cast; rfl] at hr1
    generalize 2 ^ (64 * k) = B at *
    rcases (show top1.val = 0 ∨ top1.val = 1 by omega) with ht | ht
    · rw [ht] at hr1 hXlt ⊢
      simp only [mul_zero, add_zero] at hXlt ⊢
      by_cases hRM : R < M
      · have hb1 : below.val = 1 := by rw [hbelow]; exact ite_eq_left hRM
        simp only [hb1, and_self, ↓reduceIte, Nat.cast_zero, sub_zero] at hr1
        rw [Nat.mod_eq_of_lt hRM]
        rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> push_cast at hr1 <;> omega
      · have hb0 : below.val = 0 := by rw [hbelow]; exact ite_eq_right hRM
        simp only [hb0, zero_ne_one, and_false, ↓reduceIte] at hr1
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> push_cast at hr1 <;> omega
    · rw [ht] at hr1 hXlt ⊢
      simp only [one_ne_zero, false_and, ↓reduceIte] at hr1
      simp only [mul_one] at hXlt ⊢
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> push_cast at hr1 <;> omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [Slice.length]; rw [hback, List.length_setSlice!, ht2L]; omega
  · rw [hdrop, hR1]; exact Nat.mod_lt _ hM0
  · rw [hdrop, hR1, Nat.mod_mul_mod, mul_comm, hX, Nat.add_mul_mod_self_left]

/-! ## `mul_limbs` -/

/-- Limbs of `l` from `q` up are zero. -/
def ZeroFrom (l : List U64) (q : Nat) : Prop := ∀ j, q ≤ j → l[j]!.val = 0

theorem mul_limbs_loop_spec (x y : Slice U64) (n : Usize) (hx : x.length = n.val) (hy : y.length = n.val)
    (iter : core.ops.range.Range Usize) (z : Slice U64) (hend : iter.end.val = n.val / 2)
    (hi : iter.start.val ≤ n.val / 2) (hzl : z.length = 2 * n.val)
    (hzero : ZeroFrom z.val (2 * iter.start.val + n.val))
    (hval : wordsNat z.val = wordsNat (x.val.take (2 * iter.start.val)) * wordsNat y.val) :
    low.generic.limb64.mont.mul_limbs_loop iter x y n z ⦃ r =>
      r.length = 2 * n.val ∧ ZeroFrom r.val (2 * (n.val / 2) + n.val) ∧
      wordsNat r.val = wordsNat (x.val.take (2 * (n.val / 2))) * wordsNat y.val ⦄ := by
  unfold low.generic.limb64.mont.mul_limbs_loop
  apply loop.spec_decr_nat (fun x' => n.val / 2 - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 =>
      x'.1.end.val = n.val / 2 ∧ x'.1.start.val ≤ n.val / 2 ∧ x'.2.length = 2 * n.val ∧
      ZeroFrom x'.2.val (2 * x'.1.start.val + n.val) ∧
      wordsNat x'.2.val = wordsNat (x.val.take (2 * x'.1.start.val)) * wordsNat y.val)
  · rintro ⟨it, w⟩ ⟨he, hs, hwl, hz, hv⟩
    simp only at he hs hwl hz hv
    unfold low.generic.limb64.mont.mul_limbs_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = n.val / 2 := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hz hv
      exact ⟨hwl, hz, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = 2 * n.val := hwl
      have hxL : x.val.length = n.val := hx
      have hyL : y.val.length = n.val := hy
      have hwmax : w.length ≤ Usize.max := w.property
      step as ⟨i, hi'⟩
      step as ⟨i1, hi1⟩
      step as ⟨s, back, hs', hsl, hback⟩
      step as ⟨xi, hxi⟩
      step as ⟨i3, hi3⟩
      step as ⟨xi1, hxi1⟩
      step with mul_add2_spec s y xi xi1 0#u128 (by simp) (by simp only [Slice.length] at hsl ⊢; omega)
        as ⟨rest, s1, hs1l, hs1⟩
      step as ⟨a, ha⟩
      step as ⟨z2, hz2⟩
      step as ⟨rh, hrh, _⟩
      step as ⟨i7, hi7⟩
      step as ⟨b, hb⟩
      step as ⟨s2, hs2⟩
      have hsL : s.val.length = n.val := by simp only [Slice.length] at hsl; omega
      have hs1L : s1.val.length = n.val := by simp only [Slice.length] at hs1l hsl; omega
      have hbv : (back s1).val = w.val.setSlice! i.val s1.val := by rw [hback]; simp [Slice.setSlice!_val]
      have hz2v : z2.val = (back s1).val.set (i.val + n.val) a := by rw [hz2]; simp [hi1]
      have hs2v : s2.val = z2.val.set (i.val + n.val + 1) b := by rw [hs2]; simp [hi7, hi1]
      have hbL : (back s1).val.length = 2 * n.val := by rw [hbv, List.length_setSlice!]; omega
      have hz2L : z2.val.length = 2 * n.val := by rw [hz2v, List.length_set]; exact hbL
      have hz1 : (back s1).val[i.val + n.val]!.val = 0 := by
        rw [hbv, List.getElem!_setSlice!_same _ _ _ _ (Or.inr (by omega))]; exact hz _ (by omega)
      have hz2' : z2.val[i.val + n.val + 1]!.val = 0 := by
        rw [hz2v, getElem!_set_ne' _ _ _ _ (by omega), hbv,
          List.getElem!_setSlice!_same _ _ _ _ (Or.inr (by omega))]
        exact hz _ (by omega)
      have hyt : List.take s.length y.val = y.val := List.take_of_length_le (by simp only [Slice.length]; omega)
      rw [hyt, show s.length = n.val by simp only [Slice.length]; omega] at hs1
      have hW := wordsNat_window w.val s1.val i.val (by omega)
      rw [hs1L, show w.val.slice i.val (i.val + n.val) = s.val by rw [hs', hi1]] at hW
      rw [← hbv] at hW
      have hS2 := wordsNat_set (back s1).val (i.val + n.val) a (by omega)
      rw [← hz2v, hz1] at hS2
      have hS3 := wordsNat_set z2.val (i.val + n.val + 1) b (by omega)
      rw [← hs2v, hz2'] at hS3
      have hav : a.val = rest.val % 2 ^ 64 := by rw [ha, cast_u64_val]
      have hrestb := rest.hBounds
      simp only [UScalarTy.numBits] at hrestb
      have hbv' : b.val = rest.val / 2 ^ 64 := by
        rw [hb, cast_u64_val, hrh]; simp [Nat.shiftRight_eq_div_pow]; omega
      have hrmd := Nat.mod_add_div rest.val (2 ^ 64)
      have hxi0 : xi = x.val[i.val]! := by rw [hxi, ← getElem!_pos]
      have hxi1' : xi1 = x.val[i.val + 1]! := by rw [hxi1, ← getElem!_pos, hi3]
      have hX : wordsNat (x.val.take (i.val + 2)) =
          wordsNat (x.val.take i.val) + 2 ^ (64 * i.val) * xi.val + 2 ^ (64 * (i.val + 1)) * xi1.val := by
        rw [show i.val + 2 = i.val + 1 + 1 by ring, wordsNat_take_succ' _ _ (by omega),
          wordsNat_take_succ' _ _ (by omega), hxi0, hxi1']
      refine ⟨by rw [hend1, he], by omega, ?_, ?_, ?_, by omega⟩
      · simp only [Slice.length]; rw [hs2v, List.length_set]; exact hz2L
      · intro q hq
        rw [hs2v, getElem!_set_ne' _ _ _ _ (by omega), hz2v, getElem!_set_ne' _ _ _ _ (by omega), hbv,
          List.getElem!_setSlice!_same _ _ _ _ (Or.inr (by omega))]
        exact hz _ (by omega)
      · rw [hst, show 2 * (it.start.val + 1) = i.val + 2 by omega, hX]
        rw [← hi'] at hv
        rw [hav] at hS2; rw [hbv'] at hS3
        simp only [mul_zero, add_zero] at hS2 hS3
        zify at hS3 hS2 hW hs1 hv hrmd ⊢
        linear_combination hS3 + hS2 + hW + (2 ^ (64 * i.val) : Int) * hs1 + hv +
          (2 ^ (64 * (i.val + n.val)) : Int) * hrmd
  · exact ⟨hend, hi, hzl, hzero, hval⟩

/-! ## `abs_diff` -/

theorem slice_get_spec (x : Slice U64) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice U64) x i ⦃ o => o = x.val[i.val]? ⦄ := by
  simp [core.slice.Slice.get]

@[step]
theorem copied_spec (o : Option U64) :
    core.option.OptionShared0T.copied core.marker.CopyU64 o ⦃ r => r = o ⦄ := by
  simp [core.option.OptionShared0T.copied]

theorem unwrap_get (l : List U64) (i : Nat) : core.option.Option.unwrap_or l[i]? 0#u64 = l[i]! := by
  by_cases h : i < l.length
  · simp [h, getElem!_pos, core.option.Option.unwrap_or]
  · simp [h, core.option.Option.unwrap_or]; rfl

theorem wordsNat_take_succ_any (l : List U64) (i : Nat) :
    wordsNat (l.take (i + 1)) = wordsNat (l.take i) + 2 ^ (64 * i) * l[i]!.val := by
  by_cases h : i < l.length
  · exact wordsNat_take_succ' l i h
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp [show l.length ≤ i by omega]

/-- A limb XORed with a mask: itself, or its complement. -/
theorem xor_mask_val (a flip : U64) (h : IsMask flip) :
    (a ^^^ flip).val = if flip.val = 0 then a.val else 2 ^ 64 - 1 - a.val := by
  rcases h with h | h
  · rw [UScalar.val_xor, h]; simp
  · rw [ite_eq_right_of_eq_false _ _ (by rw [h]; simp)]
    have : flip.bv = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_allOnes]; exact h
    show (a.bv ^^^ flip.bv).toNat = 2 ^ 64 - 1 - a.bv.toNat
    rw [this, BitVec.xor_allOnes, BitVec.toNat_not]

/-- The limbs of `l` XORed with a mask, read as a number: `l`, or its
complement. -/
def xorSum (flip : U64) (l : List U64) : Int :=
  if flip.val = 0 then wordsNat l else 2 ^ (64 * l.length) - 1 - wordsNat l

theorem xorSum_take_succ (flip : U64) (h : IsMask flip) (l : List U64) (i : Nat) (hi : i < l.length) :
    xorSum flip (l.take (i + 1)) = xorSum flip (l.take i) + 2 ^ (64 * i) * (l[i]! ^^^ flip).val := by
  unfold xorSum
  rw [xor_mask_val _ _ h, wordsNat_take_succ' _ _ hi]
  simp only [List.length_take, Nat.min_eq_left hi.le, Nat.min_eq_left (show i + 1 ≤ l.length by omega)]
  have := u64_lt l[i]!
  split
  · push_cast; ring
  · rw [Nat.cast_sub (by omega)]; push_cast
    rw [show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]; ring

theorem abs_diff_loop0_spec (x y : Slice U64) (h : Nat) (hx : x.length ≤ h) (hy : y.length ≤ h)
    (iter : core.ops.range.Range Usize) (z : Slice U64) (borrow : U64)
    (hend : iter.end.val = h) (hi : iter.start.val ≤ h) (hzl : z.length = h) (hb : borrow.val ≤ 1)
    (hinv : (wordsNat (z.val.take iter.start.val) : Int) - 2 ^ (64 * iter.start.val) * borrow.val =
      wordsNat (x.val.take iter.start.val) - wordsNat (y.val.take iter.start.val)) :
    low.generic.limb64.mont.abs_diff_loop0 iter z x y borrow ⦃ r =>
      r.1.length = h ∧ r.2.val ≤ 1 ∧
      (wordsNat r.1.val : Int) - 2 ^ (64 * h) * r.2.val = wordsNat x.val - wordsNat y.val ⦄ := by
  unfold low.generic.limb64.mont.abs_diff_loop0
  apply loop.spec_decr_nat (fun x' => h - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U64 =>
      x'.1.end.val = h ∧ x'.1.start.val ≤ h ∧ x'.2.1.length = h ∧ x'.2.2.val ≤ 1 ∧
      (wordsNat (x'.2.1.val.take x'.1.start.val) : Int) - 2 ^ (64 * x'.1.start.val) * x'.2.2.val =
        wordsNat (x.val.take x'.1.start.val) - wordsNat (y.val.take x'.1.start.val))
  · rintro ⟨it, w, bw⟩ ⟨he, hs, hwl, hb, hv⟩
    simp only at he hs hwl hb hv
    unfold low.generic.limb64.mont.abs_diff_loop0.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = h := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwL : w.val.length = h := hwl
      have hxL : x.val.length ≤ h := hx
      have hyL : y.val.length ≤ h := hy
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega)] at hv
      exact ⟨hwl, hb, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = h := hwl
      step with slice_get_spec x it.start as ⟨o1, ho1⟩
      step as ⟨o2, ho2⟩
      step as ⟨xi, hxi⟩
      step with slice_get_spec y it.start as ⟨o3, ho3⟩
      step as ⟨o4, ho4⟩
      step as ⟨yi, hyi⟩
      step as ⟨diff, b1, hd1⟩
      step as ⟨diff1, b2, hd2⟩
      step as ⟨w1, hw1⟩
      simp only [lift, bind_ok, WP.spec_ok]
      have hxi' : xi = x.val[it.start.val]! := by rw [hxi, ho2, ho1, unwrap_get]
      have hyi' : yi = y.val[it.start.val]! := by rw [hyi, ho4, ho3, unwrap_get]
      have hstep := sub_step xi.val yi.val bw.val diff.val diff1.val b1 b2 xi.hBounds yi.hBounds hb
        (by simpa [u64_size] using hd1) (by simpa [u64_size] using hd2)
      rw [← from_bool_val] at hstep
      have hc := sub_chain_step it.start.val hv hstep
      have hw1v : w1.val = w.val.set it.start.val diff1 := by rw [hw1]; simp
      refine ⟨by rw [hend1, he], by omega, by rw [hw1]; simp at hwl ⊢; omega,
        by rw [from_bool_val]; cases (b1 || b2) <;> simp, ?_, by omega⟩
      rw [hst, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
        List.length_take, Nat.min_eq_left (by omega), wordsNat_take_succ_any, wordsNat_take_succ_any,
        ← hxi', ← hyi']
      push_cast
      linarith
  · exact ⟨hend, hi, hzl, hb, hinv⟩

theorem abs_diff_loop1_spec (z0 : Slice U64) (flip : U64) (hf : IsMask flip) (c0 : Nat)
    (iter : core.ops.range.Range Usize) (z : Slice U64) (carry : U128)
    (hend : iter.end.val = z0.length) (hi : iter.start.val ≤ z0.length) (hzl : z.length = z0.length)
    (hc : carry.val ≤ 1) (hdrop : z.val.drop iter.start.val = z0.val.drop iter.start.val)
    (hinv : (wordsNat (z.val.take iter.start.val) : Int) + 2 ^ (64 * iter.start.val) * carry.val =
      xorSum flip (z0.val.take iter.start.val) + c0) :
    low.generic.limb64.mont.abs_diff_loop1 iter z flip carry ⦃ r =>
      r.length = z0.length ∧ ∃ c : Nat, c ≤ 1 ∧
        (wordsNat r.val : Int) + 2 ^ (64 * z0.length) * c = xorSum flip z0.val + c0 ⦄ := by
  unfold low.generic.limb64.mont.abs_diff_loop1
  apply loop.spec_decr_nat (fun x' => z0.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U128 =>
      x'.1.end.val = z0.length ∧ x'.1.start.val ≤ z0.length ∧ x'.2.1.length = z0.length ∧ x'.2.2.val ≤ 1 ∧
      x'.2.1.val.drop x'.1.start.val = z0.val.drop x'.1.start.val ∧
      (wordsNat (x'.2.1.val.take x'.1.start.val) : Int) + 2 ^ (64 * x'.1.start.val) * x'.2.2.val =
        xorSum flip (z0.val.take x'.1.start.val) + c0)
  · rintro ⟨it, w, cy⟩ ⟨he, hs, hwl, hc, hd, hv⟩
    simp only at he hs hwl hc hd hv
    unfold low.generic.limb64.mont.abs_diff_loop1.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = z0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hv
      exact ⟨hwl, cy.val, hc, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      step as ⟨zi, hzi⟩
      simp only [lift, bind_ok]
      step as ⟨w1, hw1⟩
      step as ⟨c1, hc1, _⟩
      have hzi0 : zi = z0.val[it.start.val]! := by
        rw [hzi, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      set sv := core.num.U128.wrapping_add (core.convert.num.FromU128U64.from (zi ^^^ flip)) cy with hsdef
      have hsv : sv.val = (zi ^^^ flip).val + cy.val := by
        rw [hsdef]
        have := u64_lt (zi ^^^ flip)
        simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega)]
      have hc1v : c1.val = sv.val / 2 ^ 64 := by rw [hc1]; simp [Nat.shiftRight_eq_div_pow]
      have hw1v : w1.val = w.val.set it.start.val (UScalar.cast .U64 sv) := by rw [hw1]; simp
      have hmd := Nat.mod_add_div sv.val (2 ^ 64)
      refine ⟨by rw [hend1, he], by omega, by rw [hw1]; simp at hwl ⊢; omega,
        by rw [hc1v, hsv]; have := u64_lt (zi ^^^ flip); omega, ?_, ?_, by omega⟩
      · rw [hst, hw1v, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < w.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < z0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), cast_u64_val, hc1v,
          xorSum_take_succ _ hf _ _ (by omega), ← hzi0]
        rw [show 64 * (it.start.val + 1) = 64 * it.start.val + 64 by ring, pow_add]
        zify at hmd hsv
        push_cast at hmd hsv ⊢
        linear_combination hv + (2 ^ (64 * it.start.val) : Int) * (hmd + hsv)
  · exact ⟨hend, hi, hzl, hc, hdrop, hinv⟩

theorem wordsNat_lt_of_le (l : List U64) (h : Nat) (hl : l.length ≤ h) : wordsNat l < 2 ^ (64 * h) :=
  lt_of_lt_of_le (wordsNat_lt' l) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `abs_diff`: `|x - y|` over `z`'s limbs, which `x` and `y` fit, and
whether `x < y`. -/
@[step]
theorem abs_diff_spec (z x y : Slice U64) (hx : x.length ≤ z.length) (hy : y.length ≤ z.length) :
    low.generic.limb64.mont.abs_diff z x y ⦃ r =>
      r.2.length = z.length ∧ r.1.val = (if wordsNat x.val < wordsNat y.val then 1 else 0) ∧
      wordsNat r.2.val = (if wordsNat x.val < wordsNat y.val then wordsNat y.val - wordsNat x.val
        else wordsNat x.val - wordsNat y.val) ⦄ := by
  unfold low.generic.limb64.mont.abs_diff
  step with abs_diff_loop0_spec x y z.length hx hy { start := 0#usize, «end» := z.len } z 0#u64
    (by simp) (by simp) rfl (by simp) (by simp [wordsNat_nil]) as ⟨z1, bw, hz1l, hbw, hz1⟩
  simp only [lift, bind_ok]
  step with abs_diff_loop1_spec z1 _ (neg_bit_mask bw hbw) bw.val { start := 0#usize, «end» := z1.len } z1
    (core.convert.num.FromU128U64.from bw) (by simp) (by simp) rfl (by rw [from_u128_val]; exact hbw) rfl
    (by simp [xorSum, wordsNat_nil]) as ⟨z2, hz2l, c, hc, hz2⟩
  refine ⟨by rw [hz2l, hz1l], ?_⟩
  have hX := wordsNat_lt_of_le x.val z.length hx
  have hY := wordsNat_lt_of_le y.val z.length hy
  have hZ1 := wordsNat_lt_of_le z1.val z.length (le_of_eq hz1l)
  have hZ2 := wordsNat_lt_of_le z2.val z.length (le_of_eq (hz2l.trans hz1l))
  rw [hz1l] at hz2
  unfold xorSum at hz2
  rw [neg_bit_val bw hbw] at hz2
  rw [show z1.val.length = z.length from hz1l] at hz2
  rw [show (2 : Int) ^ (64 * z.length) = ((2 ^ (64 * z.length) : Nat) : Int) by push_cast; rfl] at hz1 hz2
  generalize 2 ^ (64 * z.length) = B at *
  rcases (show bw.val = 0 ∨ bw.val = 1 by omega) with h | h
  · simp only [h, ↓reduceIte] at hz1 hz2 ⊢
    push_cast at hz1 hz2
    have hge : ¬ wordsNat x.val < wordsNat y.val := by omega
    simp only [hge, ↓reduceIte, true_and]
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> push_cast at hz2 <;> omega
  · simp only [h, one_ne_zero, ↓reduceIte] at hz1 hz2 ⊢
    push_cast at hz1 hz2
    have hlt : wordsNat x.val < wordsNat y.val := by omega
    simp only [hlt, ↓reduceIte, true_and]
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> push_cast at hz2 <;> omega

/-! ## `add_middle` -/

theorem getElem!_drop' (l : List U64) (a i : Nat) : (l.drop a)[i]! = l[a + i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

theorem add_middle_loop0_spec (z d0 : Slice U64) (h : Usize) (flip : U64) (hf : IsMask flip) (c0 : Nat)
    (hd0 : d0.length = 2 * h.val) (hz : 2 * h.val ≤ z.length) (hmax : 4 * h.val ≤ Usize.max)
    (iter : core.ops.range.Range Usize) (d : Slice U64) (carry : U128)
    (hend : iter.end.val = d0.length) (hi : iter.start.val ≤ d0.length) (hdl : d.length = d0.length)
    (hc : carry.val ≤ 3) (hdrop : d.val.drop iter.start.val = d0.val.drop iter.start.val)
    (hinv : (wordsNat (d.val.take iter.start.val) : Int) + 2 ^ (64 * iter.start.val) * carry.val =
      wordsNat (z.val.take iter.start.val) + wordsNat ((z.val.drop (2 * h.val)).take iter.start.val) +
        xorSum flip (d0.val.take iter.start.val) + c0) :
    low.generic.limb64.mont.add_middle_loop0 iter z d h flip carry ⦃ r =>
      r.1.length = d0.length ∧ r.2.val ≤ 3 ∧
      (wordsNat r.1.val : Int) + 2 ^ (64 * d0.length) * r.2.val =
        wordsNat (z.val.take d0.length) + wordsNat ((z.val.drop (2 * h.val)).take d0.length) +
          xorSum flip d0.val + c0 ⦄ := by
  unfold low.generic.limb64.mont.add_middle_loop0
  apply loop.spec_decr_nat (fun x' => d0.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U128 =>
      x'.1.end.val = d0.length ∧ x'.1.start.val ≤ d0.length ∧ x'.2.1.length = d0.length ∧ x'.2.2.val ≤ 3 ∧
      x'.2.1.val.drop x'.1.start.val = d0.val.drop x'.1.start.val ∧
      (wordsNat (x'.2.1.val.take x'.1.start.val) : Int) + 2 ^ (64 * x'.1.start.val) * x'.2.2.val =
        wordsNat (z.val.take x'.1.start.val) + wordsNat ((z.val.drop (2 * h.val)).take x'.1.start.val) +
          xorSum flip (d0.val.take x'.1.start.val) + c0)
  · rintro ⟨it, w, cy⟩ ⟨he, hs, hwl, hc, hd, hv⟩
    simp only at he hs hwl hc hd hv
    unfold low.generic.limb64.mont.add_middle_loop0.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = d0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwL : w.val.length = d0.length := hwl
      have hd0L : d0.val.length = d0.length := rfl
      rw [List.take_of_length_le (l := w.val) (by omega), List.take_of_length_le (l := d0.val) (by omega)] at hv
      exact ⟨hwl, hc, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = d0.length := hwl
      have hd0L : d0.val.length = d0.length := rfl
      have hzL : z.val.length = z.length := rfl
      have hzmax : z.length ≤ Usize.max := z.property
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step with slice_get_spec as ⟨o1, ho1⟩
      step as ⟨o2, ho2⟩
      step as ⟨zh, hzh⟩
      step as ⟨zi, hzi⟩
      simp only [lift, bind_ok]
      step as ⟨di, hdi⟩
      step as ⟨w1, hw1⟩
      step as ⟨c1, hc1, _⟩
      have hzh' : zh = (z.val.drop (2 * h.val))[it.start.val]! := by
        rw [hzh, ho2, ho1, unwrap_get, getElem!_drop', hi2, hi1]
      have hzi' : zi = z.val[it.start.val]! := by rw [hzi, ← getElem!_pos]
      have hdi0 : di = d0.val[it.start.val]! := by
        rw [hdi, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      set sv := core.num.U128.wrapping_add (core.num.U128.wrapping_add (core.num.U128.wrapping_add
        (core.convert.num.FromU128U64.from zi) (core.convert.num.FromU128U64.from zh))
        (core.convert.num.FromU128U64.from (di ^^^ flip))) cy with hsdef
      have hsv : sv.val = zi.val + zh.val + (di ^^^ flip).val + cy.val := by
        rw [hsdef]
        have := u64_lt zi; have := u64_lt zh; have := u64_lt (di ^^^ flip)
        simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hc1v : c1.val = sv.val / 2 ^ 64 := by rw [hc1]; simp [Nat.shiftRight_eq_div_pow]
      have hw1v : w1.val = w.val.set it.start.val (UScalar.cast .U64 sv) := by rw [hw1]; simp
      have hmd := Nat.mod_add_div sv.val (2 ^ 64)
      refine ⟨by rw [hend1, he], by omega, by rw [hw1]; simp at hwl ⊢; omega,
        by rw [hc1v, hsv]; have := u64_lt zi; have := u64_lt zh; have := u64_lt (di ^^^ flip); omega,
        ?_, ?_, by omega⟩
      · rw [hst, hw1v, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < w.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < d0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), cast_u64_val, hc1v,
          xorSum_take_succ _ hf _ _ (by omega), ← hdi0, wordsNat_take_succ_any, wordsNat_take_succ_any,
          ← hzi', ← hzh']
        rw [show 64 * (it.start.val + 1) = 64 * it.start.val + 64 by ring, pow_add]
        zify at hmd hsv
        push_cast at hmd hsv ⊢
        linear_combination hv + (2 ^ (64 * it.start.val) : Int) * (hmd + hsv)
  · exact ⟨hend, hi, hdl, hc, hdrop, hinv⟩

/-- What `add_middle`'s second loop adds over its first `i` limbs: `d`'s,
then `top` above them. -/
def aSum (d : List U64) (top : Nat) (i : Nat) : Nat :=
  wordsNat (d.take i) + if d.length < i then 2 ^ (64 * d.length) * top else 0

theorem aSum_succ (d : List U64) (top i : Nat) :
    aSum d top (i + 1) = aSum d top i +
      2 ^ (64 * i) * (if i < d.length then d[i]!.val else if i = d.length then top else 0) := by
  unfold aSum
  rcases Nat.lt_trichotomy i d.length with h | h | h
  · rw [wordsNat_take_succ' _ _ h]
    simp [h, show ¬ d.length < i + 1 by omega, show ¬ d.length < i by omega]
  · subst h
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp [h, show d.length < i + 1 by omega, show ¬ i < d.length by omega, show i ≠ d.length by omega]

theorem add_middle_loop1_spec (z0 d : Slice U64) (h : Usize) (top : U128) (htop : top.val < 2 ^ 64)
    (hh : h.val ≤ z0.length)
    (iter : core.ops.range.Range Usize) (z : Slice U64) (carry : U128)
    (hend : iter.end.val = z0.length - h.val) (hi : iter.start.val ≤ z0.length - h.val)
    (hzl : z.length = z0.length) (hc : carry.val ≤ 1)
    (hdrop : z.val.drop (h.val + iter.start.val) = z0.val.drop (h.val + iter.start.val))
    (hinv : wordsNat (z.val.take (h.val + iter.start.val)) + 2 ^ (64 * (h.val + iter.start.val)) * carry.val =
      wordsNat (z0.val.take (h.val + iter.start.val)) + 2 ^ (64 * h.val) * aSum d.val top.val iter.start.val) :
    low.generic.limb64.mont.add_middle_loop1 iter z d h top carry ⦃ r =>
      r.length = z0.length ∧ ∃ c : Nat, c ≤ 1 ∧
        wordsNat r.val + 2 ^ (64 * z0.length) * c =
          wordsNat z0.val + 2 ^ (64 * h.val) * aSum d.val top.val (z0.length - h.val) ⦄ := by
  unfold low.generic.limb64.mont.add_middle_loop1
  apply loop.spec_decr_nat (fun x' => z0.length - h.val - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U128 =>
      x'.1.end.val = z0.length - h.val ∧ x'.1.start.val ≤ z0.length - h.val ∧ x'.2.1.length = z0.length ∧
      x'.2.2.val ≤ 1 ∧
      x'.2.1.val.drop (h.val + x'.1.start.val) = z0.val.drop (h.val + x'.1.start.val) ∧
      wordsNat (x'.2.1.val.take (h.val + x'.1.start.val)) + 2 ^ (64 * (h.val + x'.1.start.val)) * x'.2.2.val =
        wordsNat (z0.val.take (h.val + x'.1.start.val)) + 2 ^ (64 * h.val) * aSum d.val top.val x'.1.start.val)
  · rintro ⟨it, w, cy⟩ ⟨he, hs, hwl, hc, hd, hv⟩
    simp only at he hs hwl hc hd hv
    unfold low.generic.limb64.mont.add_middle_loop1.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = z0.length - h.val := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      rw [show h.val + (z0.length - h.val) = z0.length by omega] at hv
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hv
      exact ⟨hwl, cy.val, hc, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      have hwmax : w.length ≤ Usize.max := w.property
      -- The limb added at `i`: `d`'s, then `top`, then nothing.
      have hadd :
          (match compare it.start.val d.len.val with
            | Ordering.lt => do
              let i2 ← d.index_usize it.start
              ok (core.convert.num.FromU128U64.from i2)
            | Ordering.eq => ok top
            | Ordering.gt => ok 0#u128) ⦃ a => a.val < 2 ^ 64 ∧
            a.val = (if it.start.val < d.val.length then d.val[it.start.val]!.val
              else if it.start.val = d.val.length then top.val else 0) ⦄ := by
        have hdL : d.len.val = d.val.length := by simp [Slice.len]
        split
        · rename_i hcmp
          rw [Nat.compare_eq_lt, hdL] at hcmp
          step as ⟨di, hdi⟩
          refine ⟨?_, ?_⟩
          · rw [from_u128_val]; exact u64_lt di
          · rw [from_u128_val, ite_eq_left_of_eq_true _ _ (eq_true hcmp), hdi, ← getElem!_pos]
        · rename_i hcmp
          rw [Nat.compare_eq_eq, hdL] at hcmp
          simp only [WP.spec_ok]
          exact ⟨htop, by simp [hcmp]⟩
        · rename_i hcmp
          rw [Nat.compare_eq_gt, hdL] at hcmp
          simp only [WP.spec_ok]
          exact ⟨by simp, by simp [show ¬ it.start.val < d.val.length by omega,
            show it.start.val ≠ d.val.length by omega]⟩
      simp only [lift, bind_ok]
      apply WP.spec_bind hadd
      rintro a ⟨ha, hav⟩
      step as ⟨i2, hi2⟩
      step as ⟨zi, hzi⟩
      step as ⟨w1, hw1⟩
      step as ⟨c1, hc1, _⟩
      have hi2v : i2.val = h.val + it.start.val := hi2
      have hzi0 : zi = z0.val[h.val + it.start.val]! := by
        rw [hzi, ← getElem!_pos, hi2v]; exact getElem!_of_drop_eq hd
      set sv := core.num.U128.wrapping_add (core.num.U128.wrapping_add (core.convert.num.FromU128U64.from zi) a)
        cy with hsdef
      have hsv : sv.val = zi.val + a.val + cy.val := by
        rw [hsdef]
        have := u64_lt zi
        simp only [core.num.U128.wrapping_add_val_eq, from_u128_val, UScalar.size, UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hc1v : c1.val = sv.val / 2 ^ 64 := by rw [hc1]; simp [Nat.shiftRight_eq_div_pow]
      have hw1v : w1.val = w.val.set (h.val + it.start.val) (UScalar.cast .U64 sv) := by
        rw [hw1]; simp [hi2v]
      have hmd := Nat.mod_add_div sv.val (2 ^ 64)
      refine ⟨by rw [hend1, he], by omega, by rw [hw1]; simp at hwl ⊢; omega,
        by rw [hc1v, hsv]; have := u64_lt zi; omega, ?_, ?_, by omega⟩
      · rw [hst, ← Nat.add_assoc, hw1v, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show h.val + it.start.val < w.val.length by omega),
          List.drop_eq_getElem_cons (show h.val + it.start.val < z0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, ← Nat.add_assoc, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons,
          wordsNat_nil, List.length_take, Nat.min_eq_left (by omega), cast_u64_val, hc1v,
          wordsNat_take_succ' _ _ (by omega), aSum_succ, ← hzi0, ← hav]
        rw [show 64 * (h.val + it.start.val + 1) = 64 * (h.val + it.start.val) + 64 by ring, pow_add,
          show 64 * (h.val + it.start.val) = 64 * h.val + 64 * it.start.val by ring, pow_add] at *
        zify at hmd hsv hv ⊢
        push_cast at hmd hsv hv ⊢
        linear_combination hv + (2 ^ (64 * h.val) * 2 ^ (64 * it.start.val) : Int) * (hmd + hsv)
  · exact ⟨hend, hi, hzl, hc, hdrop, hinv⟩

/-- `add_middle`: adds `M = z0 + z2 ± d` at limb `h` of a Karatsuba product
`z`, whose low `2h` limbs hold `z0` and the rest `z2`, for a sum that fits
`z`. -/
@[step]
theorem add_middle_spec (z d : Slice U64) (h : Usize) (negative : U64) (hneg : negative.val ≤ 1)
    (hd : d.length = 2 * h.val) (hz : 3 * h.val < z.length) (hz4 : z.length ≤ 4 * h.val)
    (hmax : 4 * h.val ≤ Usize.max) (M : Nat)
    (hM : (M : Int) = wordsNat (z.val.take (2 * h.val)) + wordsNat (z.val.drop (2 * h.val)) +
      (if negative.val = 0 then (wordsNat d.val : Int) else -(wordsNat d.val : Int)))
    (hfit : wordsNat z.val + 2 ^ (64 * h.val) * M < 2 ^ (64 * z.length)) :
    low.generic.limb64.mont.add_middle z d h negative ⦃ r =>
      r.1.length = z.length ∧ r.2.length = d.length ∧
        wordsNat r.1.val = wordsNat z.val + 2 ^ (64 * h.val) * M ⦄ := by
  unfold low.generic.limb64.mont.add_middle
  simp only [lift, bind_ok]
  step with add_middle_loop0_spec z d h (core.num.U64.wrapping_sub 0#u64 negative) (neg_bit_mask negative hneg)
    negative.val hd (by omega) hmax { start := 0#usize, «end» := d.len } d (core.convert.num.FromU128U64.from negative)
    (by simp) (by simp) rfl (by rw [from_u128_val]; omega) rfl
    (by simp [xorSum, wordsNat_nil]) as ⟨d1, carry1, hd1l, hc1, hd1⟩
  have hzL : z.val.length = z.length := rfl
  have hdL : d.val.length = d.length := rfl
  rw [hd, List.take_of_length_le (l := z.val.drop (2 * h.val)) (by simp; omega)] at hd1
  unfold xorSum at hd1
  rw [neg_bit_val negative hneg, hdL, hd] at hd1
  have hD1 := wordsNat_lt_of_le d1.val (2 * h.val) (by rw [show d1.val.length = d1.length from rfl, hd1l, hd])
  -- `M = d1 + 2^(128h) (carry1 - negative)`, so `carry1 ≥ negative`.
  have hmid : (M : Int) = wordsNat d1.val + 2 ^ (64 * (2 * h.val)) * ((carry1.val : Int) - negative.val) := by
    rw [hM]
    rcases (show negative.val = 0 ∨ negative.val = 1 by omega) with hn | hn <;>
      simp only [hn, ↓reduceIte, one_ne_zero] at hd1 ⊢ <;> push_cast at hd1 ⊢ <;> linear_combination -hd1
  have hge : negative.val ≤ carry1.val := by
    rw [show (2 : Int) ^ (64 * (2 * h.val)) = ((2 ^ (64 * (2 * h.val)) : Nat) : Int) by push_cast; rfl] at hmid
    generalize 2 ^ (64 * (2 * h.val)) = B at *
    by_contra hlt
    have : (B : Int) * ((carry1.val : Int) - negative.val) ≤ -B := by
      have : (carry1.val : Int) - negative.val ≤ -1 := by omega
      nlinarith
    omega
  set top := core.num.U128.wrapping_sub carry1 (core.convert.num.FromU128U64.from negative) with htopdef
  have htop : top.val = carry1.val - negative.val := by
    rw [htopdef, core.num.U128.wrapping_sub_val_eq, from_u128_val]
    simp only [UScalar.size, UScalarTy.numBits]
    omega
  step as ⟨i3, hi3⟩
  step with add_middle_loop1_spec z d1 h top (by omega) (by omega) { start := 0#usize, «end» := i3 } z 0#u128
    (by simp [hi3]) (by simp) rfl (by simp) rfl (by simp [aSum, wordsNat_nil]) as ⟨z1, hz1l, c, hc, hz1⟩
  have hd1L : d1.val.length = 2 * h.val := by rw [show d1.val.length = d1.length from rfl, hd1l, hd]
  unfold aSum at hz1
  rw [List.take_of_length_le (by omega), ite_eq_left (by omega), hd1L] at hz1
  have hMn : M = wordsNat d1.val + 2 ^ (64 * (2 * h.val)) * top.val := by
    zify [hge] at htop ⊢; rw [hmid, htop]
  rw [← hMn] at hz1
  refine ⟨hz1l, by rw [hd1l], ?_⟩
  have hZ1 := wordsNat_lt_of_le z1.val z.length (le_of_eq hz1l)
  have hc0 : c = 0 := by
    by_contra hc0
    have : 2 ^ (64 * z.length) ≤ 2 ^ (64 * z.length) * c := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [hc0] at hz1; simpa using hz1

/-! ## `mul_limbs` -/

/-- The scratch `mul_limbs` takes at `n` limbs: a Karatsuba split at
`h = ceil(n / 2)` takes `4h` and its halves' scratch. -/
def mulNeed (n : Nat) : Nat := if n < 32 then 0 else 4 * ((n + 1) / 2) + mulNeed ((n + 1) / 2)
termination_by n
decreasing_by omega

theorem mulNeed_mono (b : Nat) : ∀ a ≤ b, mulNeed a ≤ mulNeed b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rw [mulNeed.eq_1 a, mulNeed.eq_1 b]
    split <;> split
    · omega
    · omega
    · omega
    · have := ih ((b + 1) / 2) (by omega) ((a + 1) / 2) (by omega); omega

theorem karatsuba_mul_eq : low.generic.limb64.mont.KARATSUBA_MUL = 32#usize := by
  unfold low.generic.limb64.mont.KARATSUBA_MUL; rfl

/-- `x0 y1 + x1 y0 = x0 y0 + x1 y1 + (x0 - x1)(y1 - y0)`, the last by its
magnitude and sign. -/
theorem karatsuba_mid (x0 x1 y0 y1 : Nat) :
    ((x0 * y1 + x1 * y0 : Nat) : Int) = (x0 * y0 : Nat) + (x1 * y1 : Nat) +
      (if ((if x0 < x1 then 1 else 0) ^^^ (if y1 < y0 then 1 else 0) : Nat) = 0 then
        (((if x0 < x1 then x1 - x0 else x0 - x1) * (if y1 < y0 then y0 - y1 else y1 - y0) : Nat) : Int)
      else -(((if x0 < x1 then x1 - x0 else x0 - x1) * (if y1 < y0 then y0 - y1 else y1 - y0) : Nat) : Int)) := by
  by_cases h1 : x0 < x1 <;> by_cases h2 : y1 < y0
  · simp only [h1, h2, ↓reduceIte, show (1 : Nat) ^^^ 1 = 0 by rfl]
    push_cast [Nat.cast_sub h1.le, Nat.cast_sub h2.le]; ring
  · simp only [h1, h2, ↓reduceIte, show (1 : Nat) ^^^ 0 = 1 by rfl, one_ne_zero]
    push_cast [Nat.cast_sub h1.le, Nat.cast_sub (not_lt.mp h2)]; ring
  · simp only [h1, h2, ↓reduceIte, show (0 : Nat) ^^^ 1 = 1 by rfl, one_ne_zero]
    push_cast [Nat.cast_sub (not_lt.mp h1), Nat.cast_sub h2.le]; ring
  · simp only [h1, h2, ↓reduceIte, show (0 : Nat) ^^^ 0 = 0 by rfl]
    push_cast [Nat.cast_sub (not_lt.mp h1), Nat.cast_sub (not_lt.mp h2)]; ring

theorem setSlice_zero_full {α : Type} (s w : List α) (h : w.length = s.length) : s.setSlice! 0 w = w := by
  rw [setSlice_eq s w 0 (by omega)]; simp [h]

set_option maxHeartbeats 1000000 in
/-- `mul_limbs`: `z := x y` for `x` and `y` of `n` limbs, `z` of `2n`, and
the scratch Karatsuba takes from `KARATSUBA_MUL` limbs. -/
theorem mul_limbs_spec (n : Nat) : ∀ (z x y scratch : Slice U64), x.length = n → y.length = n →
    z.length = 2 * n → mulNeed n ≤ scratch.length → 4 * n ≤ Usize.max →
    low.generic.limb64.mont.mul_limbs z x y scratch ⦃ r =>
      r.1.length = 2 * n ∧ r.2.length = scratch.length ∧ wordsNat r.1.val = wordsNat x.val * wordsNat y.val ⦄ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z x y scratch hx hy hz hs hmax
  have hxL : x.val.length = n := hx
  have hyL : y.val.length = n := hy
  have hzL : z.val.length = 2 * n := hz
  rw [low.generic.limb64.mont.mul_limbs]
  have hlen : (Slice.len x).val = n := by simp only [Slice.len_val]; exact hx
  step as ⟨i, hi⟩
  step as ⟨z1, back, hz1, hz1l, hback⟩
  have hz1v : z1.val = z.val := by
    rw [hz1, List.slice, hi]; simp [hzL, hlen]
  rw [karatsuba_mul_eq]
  split
  · rename_i hn
    have hn' : n < 32 := by rw [← hlen]; simpa using hn
    clear ih
    have hiv : i.val = 2 * n := by rw [hi, hlen]
    step as ⟨z2, hz2l, hz2⟩
    step as ⟨i1, hi1⟩
    step with mul_limbs_loop_spec x y (Slice.len x) (by rw [hlen]; exact hx) (by rw [hlen]; exact hy)
      { start := 0#usize, «end» := i1 } z2 (by simp [hi1]) (by simp) (by rw [hz2l, hz1l, hiv, hlen])
      (by intro j _; rw [hz2]; by_cases hj : j < z1.length <;> simp [hj])
      (by rw [hz2, wordsNat_replicate_zero]; simp [wordsNat_nil]) as ⟨z3, hz3l, hz3z, hz3⟩
    rw [hlen] at hz3l hz3z hz3
    have hz3L : z3.val.length = 2 * n := hz3l
    step as ⟨i2, hi2⟩
    split
    · rename_i hodd
      have hodd' : n % 2 = 1 := by have := congrArg UScalar.val hodd; rw [hi2, hlen] at this; simpa using this
      rw [show 2 * (n / 2) = n - 1 by omega] at hz3z hz3
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨sw, back1, hsw, hswl, hback1⟩
      step as ⟨xi, hxi⟩
      step with mul_add_spec sw y xi (by rw [hswl, hi5, hi4, hi3, hlen, hy]; omega) as ⟨c, s1, hs1l, hc, hs1⟩
      step as ⟨i8, hi8⟩
      simp only [lift, bind_ok]
      step as ⟨z5, hz5⟩
      have hi3v : i3.val = n - 1 := by rw [hi3, hlen]
      have hi5v : i5.val = 2 * n - 1 := by rw [hi5, hi4, hlen]
      have hi8v : i8.val = 2 * n - 1 := by rw [hi8, hi4, hlen]
      have hswL : sw.length = n := by rw [hswl, hi5v, hi3v]; omega
      have hs1L : s1.val.length = n := by rw [show s1.val.length = s1.length from rfl, hs1l, hswL]
      have hz4 : (back1 s1).val = z3.val.setSlice! (n - 1) s1.val := by rw [hback1, Slice.setSlice!_val, hi3v]
      have hz5v : z5.val = (z3.val.setSlice! (n - 1) s1.val).set (2 * n - 1) (UScalar.cast .U64 c) := by
        rw [hz5, Slice.set_val_eq, hz4, hi8v]
      have hwin := wordsNat_window z3.val s1.val (n - 1) (by rw [hs1L, hz3L]; omega)
      rw [hi3v, hi5v] at hsw
      rw [hs1L, show n - 1 + n = 2 * n - 1 by omega, ← hsw] at hwin
      have hset := wordsNat_set (z3.val.setSlice! (n - 1) s1.val) (2 * n - 1) (UScalar.cast .U64 c) (by simp; omega)
      rw [List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hs1L]; omega), hz3z _ (by omega), ← hz5v,
        cast_u64_val, Nat.mod_eq_of_lt hc] at hset
      have hxi' : xi = x.val[n - 1]! := by rw [hxi, ← getElem!_pos, hi3v]
      have hxs := wordsNat_take_succ' x.val (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega, List.take_of_length_le (by omega), ← hxi'] at hxs
      rw [hswL] at hs1
      have hb := hback z5
      have hz5L : z5.val.length = 2 * n := by rw [hz5v]; simp [hz3L]
      rw [setSlice_zero_full _ _ (by rw [hz5L, hzL])] at hb
      refine ⟨by simp only [Slice.length]; rw [hb, hz5L], ?_⟩
      rw [hb]
      have hab : (2 : Nat) ^ (64 * (2 * n - 1)) = 2 ^ (64 * (n - 1)) * 2 ^ (64 * n) := by
        rw [← pow_add]; congr 1; omega
      rw [hab] at hset
      zify at hset hwin hs1 hz3 hxs ⊢
      linear_combination hset + hwin + (2 ^ (64 * (n - 1)) : Int) * hs1 + hz3 - (wordsNat y.val : Int) * hxs
    · rename_i heven
      have heven' : n % 2 = 0 := by
        have : i2.val ≠ 1 := fun h => heven (UScalar.eq_of_val_eq (by rw [h]; rfl))
        rw [hi2, hlen] at this; omega
      rw [show 2 * (n / 2) = n by omega, List.take_of_length_le (by omega)] at hz3
      simp only [WP.spec_ok]
      have hb := hback z3
      rw [setSlice_zero_full _ _ (by rw [hz3L, hzL])] at hb
      refine ⟨by simp only [Slice.length]; rw [hb, hz3L], by simp, by rw [hb, hz3]⟩
  · rename_i hn
    have hn' : 32 ≤ n := by rw [← hlen]; simpa using hn
    have hdc : core.num.Usize.div_ceil (Slice.len x) 2#usize ⦃ r => r.val = (n + 1) / 2 ⦄ := by
      simp [core.num.Usize.div_ceil, WP.spec_ok, hlen]
    step with hdc as ⟨h, hh⟩
    have hneed : mulNeed n = 4 * h.val + mulNeed h.val := by
      rw [mulNeed.eq_1, hh]; simp [show ¬ n < 32 by omega]
    have hzz : z1.length = 2 * n := by rw [hz1l, hi, hlen]
    step with core.slice.Slice.split_at_mut.spec scratch h (by omega) as ⟨dx, rest, smb, hdxl, hrestl, _, _, hsmb⟩
    step with core.slice.Slice.split_at_mut.spec rest h (by omega) as ⟨dy, rest1, smb1, hdyl, hrest1l, _, _, hsmb1⟩
    step as ⟨i1, hi1⟩
    step with core.slice.Slice.split_at_mut.spec rest1 i1 (by omega) as ⟨d, rest2, smb2, hdl, hrest2l, _, _, hsmb2⟩
    step with core.slice.Slice.split_at.spec x h (by omega) as ⟨x0, x1, hx0l, hx1l, hx0, hx1⟩
    step with core.slice.Slice.split_at.spec y h (by omega) as ⟨y0, y1, hy0l, hy1l, hy0, hy1⟩
    step with abs_diff_spec dx x0 x1 (by omega) (by omega) as ⟨sx, dx1, hdx1l, hsx, hdx1⟩
    step with abs_diff_spec dy y1 y0 (by omega) (by omega) as ⟨sy, dy1, hdy1l, hsy, hdy1⟩
    simp only [lift, bind_ok]
    step with ih h.val (by omega) d dx1 dy1 rest2 (by omega) (by omega) (by omega) (by omega) (by omega)
      as ⟨d1, rest3, hd1l, hrest3l, hd1⟩
    step with core.slice.Slice.split_at_mut.spec z1 i1 (by omega) as ⟨z0, z2, smb3, hz0l, hz2l, hz0, hz2, hsmb3⟩
    step with ih h.val (by omega) z0 x0 y0 rest3 (by omega) (by omega) (by omega) (by omega) (by omega)
      as ⟨z01, rest4, hz01l, hrest4l, hz01⟩
    have hx1n : x1.length = n - h.val := by rw [hx1l, hx]
    have hy1n : y1.length = n - h.val := by rw [hy1l, hy]
    have hz2n : z2.length = 2 * (n - h.val) := by rw [hz2l, hzz, hi1]; omega
    have hr4 : mulNeed (n - h.val) ≤ rest4.length := by
      have h1 := mulNeed_mono h.val (n - h.val) (by omega)
      have h2 : mulNeed h.val ≤ rest4.length := by omega
      exact le_trans h1 h2
    have hm4 : 4 * (n - h.val) ≤ Usize.max := by omega
    step with ih (n - h.val) (by omega) z2 x1 y1 rest4 hx1n hy1n hz2n hr4 hm4
      as ⟨z21, rest5, hz21l, hrest5l, hz21⟩
    obtain ⟨hz3v, hz3l⟩ := hsmb3 z01 z21 (by omega) (by omega)
    -- The halves' values.
    have hX : wordsNat x.val = wordsNat x0.val + 2 ^ (64 * h.val) * wordsNat x1.val := by
      conv_lhs => rw [← List.take_append_drop h.val x.val]
      rw [wordsNat_append, List.length_take, Nat.min_eq_left (by omega), hx0, hx1]
    have hY : wordsNat y.val = wordsNat y0.val + 2 ^ (64 * h.val) * wordsNat y1.val := by
      conv_lhs => rw [← List.take_append_drop h.val y.val]
      rw [wordsNat_append, List.length_take, Nat.min_eq_left (by omega), hy0, hy1]
    have hxs : (sx ^^^ sy).val = ((if wordsNat x0.val < wordsNat x1.val then 1 else 0) ^^^
        (if wordsNat y1.val < wordsNat y0.val then 1 else 0) : Nat) := by
      rw [UScalar.val_xor, hsx, hsy]
    have hneg : (sx ^^^ sy).val ≤ 1 := by rw [hxs]; split_ifs <;> decide
    have hz3L : (smb3 (z01, z21)).length = 2 * n := by rw [hz3l, hzz]
    have hz01L : z01.val.length = 2 * h.val := hz01l
    have hM := karatsuba_mid (wordsNat x0.val) (wordsNat x1.val) (wordsNat y0.val) (wordsNat y1.val)
    rw [← hdx1, ← hdy1, ← hd1, ← hxs, ← hz01, ← hz21] at hM
    have hprod : wordsNat z01.val + 2 ^ (64 * (2 * h.val)) * wordsNat z21.val +
        2 ^ (64 * h.val) * (wordsNat x0.val * wordsNat y1.val + wordsNat x1.val * wordsNat y0.val) =
        wordsNat x.val * wordsNat y.val := by
      rw [hz01, hz21, hX, hY, show 64 * (2 * h.val) = 64 * h.val + 64 * h.val by ring, pow_add]; ring
    have hXY : wordsNat x.val * wordsNat y.val < 2 ^ (64 * (2 * n)) := by
      have hx' := wordsNat_lt' x.val
      have hy' := wordsNat_lt' y.val
      rw [hxL] at hx'; rw [hyL] at hy'
      rw [show 64 * (2 * n) = 64 * n + 64 * n by ring, pow_add]
      exact Nat.mul_lt_mul'' hx' hy'
    step with add_middle_spec (smb3 (z01, z21)) d1 h (sx ^^^ sy) hneg hd1l (by omega) (by omega) (by omega)
      (wordsNat x0.val * wordsNat y1.val + wordsNat x1.val * wordsNat y0.val)
      (by rw [hz3v, ← hz01L, List.take_left, List.drop_left]; exact hM)
      (by rw [hz3v, wordsNat_append, hz01L, hz3L]; omega) as ⟨z4, d2, hz4l, hd2l, hz4⟩
    have hz4L : z4.val.length = 2 * n := by rw [show z4.val.length = z4.length from rfl, hz4l, hz3L]
    have hb := hback z4
    rw [setSlice_zero_full _ _ (by rw [hz4L, hzL])] at hb
    have hr6 := (hsmb2 d2 rest5 (by omega) (by omega)).2
    have hr7 := (hsmb1 dy1 (smb2 (d2, rest5)) (by omega) (by omega)).2
    have hr8 := (hsmb dx1 (smb1 (dy1, smb2 (d2, rest5))) (by omega) (by omega)).2
    refine ⟨by simp only [Slice.length]; rw [hb, hz4L], hr8, ?_⟩
    rw [hb, hz4, hz3v, wordsNat_append, hz01L, ← hprod]

/-! ## `sqr_limbs` -/

/-- `x`'s products of two different limbs from its first `r` rows: `x[i] x[k]`
at `2^(64(i + k))` for `i < r` and `k > i`. -/
def offSum (x : List U64) : Nat → Nat
  | 0 => 0
  | r + 1 => offSum x r + x[r]!.val * 2 ^ (64 * (2 * r + 1)) * wordsNat (x.drop (r + 1))

theorem wordsNat_drop_succ (l : List U64) (r : Nat) (h : r < l.length) :
    wordsNat (l.drop r) = l[r]!.val + 2 ^ 64 * wordsNat (l.drop (r + 1)) := by
  rw [List.drop_eq_getElem_cons h, wordsNat_cons, getElem!_pos l r h]

set_option maxHeartbeats 1000000 in
theorem sqr_limbs_loop0_spec (x : Slice U64) (n : Usize) (hx : x.length = n.val)
    (iter : core.ops.range.Range Usize) (z : Slice U64) (hend : iter.end.val = n.val / 2)
    (hi : iter.start.val ≤ n.val / 2) (hzl : z.length = 2 * n.val)
    (hzero : ZeroFrom z.val (2 * iter.start.val + n.val))
    (hval : wordsNat z.val = offSum x.val (2 * iter.start.val)) :
    low.generic.limb64.mont.sqr_limbs_loop0 iter x n z ⦃ r =>
      r.length = 2 * n.val ∧ wordsNat r.val = offSum x.val (2 * (n.val / 2)) ⦄ := by
  unfold low.generic.limb64.mont.sqr_limbs_loop0
  apply loop.spec_decr_nat (fun x' => n.val / 2 - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 =>
      x'.1.end.val = n.val / 2 ∧ x'.1.start.val ≤ n.val / 2 ∧ x'.2.length = 2 * n.val ∧
      ZeroFrom x'.2.val (2 * x'.1.start.val + n.val) ∧
      wordsNat x'.2.val = offSum x.val (2 * x'.1.start.val))
  · rintro ⟨it, w⟩ ⟨he, hs, hwl, hz, hv⟩
    simp only at he hs hwl hz hv
    unfold low.generic.limb64.mont.sqr_limbs_loop0.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = n.val / 2 := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      exact ⟨hwl, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = 2 * n.val := hwl
      have hxL : x.val.length = n.val := hx
      have hwmax : w.length ≤ Usize.max := w.property
      step as ⟨i, hi'⟩
      step as ⟨xi, hxi⟩
      step as ⟨i2, hi2⟩
      step as ⟨xi1, hxi1⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨zo, hzo⟩
      step with mul_add_limb_spec xi xi1 zo 0#u128 (by simp) as ⟨sv, hsv⟩
      step as ⟨i7, hi7⟩
      simp only [lift, bind_ok]
      step as ⟨z1, hz1⟩
      step as ⟨i9, hi9⟩
      step as ⟨i10, hi10⟩
      step as ⟨s1, back, hs1, hs1l, hback⟩
      step as ⟨i11, hi11⟩
      step as ⟨s2, hs2, hs2l⟩
      step as ⟨xi1', hxi1'⟩
      step as ⟨c, hc, _⟩
      have hiv : i.val = 2 * it.start.val := hi'
      have hi1n : i.val + 1 < n.val := by omega
      have hsvb : sv.val < 2 ^ 128 := by have := sv.hBounds; simpa using this
      have hcv : c.val = sv.val / 2 ^ 64 := by rw [hc]; simp [Nat.shiftRight_eq_div_pow]
      have hs1L : s1.length = n.val - i.val - 2 := by rw [hs1l, hi10, hi9, hi4]; omega
      have hs2L : s2.length = n.val - i.val - 2 := by rw [hs2l, hi11, hx]; omega
      step with mul_add2_spec s1 s2 xi xi1' c (by rw [hcv]; omega) (by omega) as ⟨rest, s3, hs3l, hs3⟩
      step as ⟨z3, hz3⟩
      step as ⟨rh, hrh, _⟩
      step as ⟨i16, hi16⟩
      step as ⟨s4, hs4⟩
      set L := n.val - i.val - 2 with hL
      rw [List.take_of_length_le (by simp only [Slice.length] at hs1L hs2L ⊢; omega), hs1L] at hs3
      have hs3L : s3.val.length = L := by rw [show s3.val.length = s3.length from rfl, hs3l, hs1L]
      have hz1v : z1.val = w.val.set (2 * i.val + 1) (UScalar.cast .U64 sv) := by rw [hz1]; simp [hi7, hi4]
      have hbv : (back s3).val = z1.val.setSlice! (2 * i.val + 2) s3.val := by
        rw [hback]; simp [Slice.setSlice!_val, hi9, hi4]
      have hz3v : z3.val = (back s3).val.set (i.val + n.val) (UScalar.cast .U64 rest) := by rw [hz3]; simp [hi10]
      have hs4v : s4.val = z3.val.set (i.val + n.val + 1) (UScalar.cast .U64 rh) := by
        rw [hs4]; simp [hi16, hi10]
      have hz1L : z1.val.length = 2 * n.val := by rw [hz1v, List.length_set]; exact hwL
      have hbL : (back s3).val.length = 2 * n.val := by rw [hbv, List.length_setSlice!]; exact hz1L
      have hz3L : z3.val.length = 2 * n.val := by rw [hz3v, List.length_set]; exact hbL
      have hzo' : zo = w.val[2 * i.val + 1]! := by rw [hzo, ← getElem!_pos, hi5, hi4]
      have hxi' : xi = x.val[i.val]! := by rw [hxi, ← getElem!_pos]
      have hxi1v : xi1 = x.val[i.val + 1]! := by rw [hxi1, ← getElem!_pos, hi2]
      have hxi1'' : xi1' = xi1 := by rw [hxi1', hxi1]
      have hb0 : (back s3).val[i.val + n.val]!.val = 0 := by
        rw [hbv, List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hs3L]; omega), hz1v,
          getElem!_set_ne' _ _ _ _ (by omega)]
        exact hz _ (by omega)
      have hz30 : z3.val[i.val + n.val + 1]!.val = 0 := by
        rw [hz3v, getElem!_set_ne' _ _ _ _ (by omega), hbv,
          List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hs3L]; omega), hz1v, getElem!_set_ne' _ _ _ _ (by omega)]
        exact hz _ (by omega)
      have hS1 := wordsNat_set w.val (2 * i.val + 1) (UScalar.cast .U64 sv) (by omega)
      rw [← hz1v, ← hzo', cast_u64_val] at hS1
      have hW := wordsNat_window z1.val s3.val (2 * i.val + 2) (by rw [hs3L, hz1L]; omega)
      rw [hs3L, show 2 * i.val + 2 + L = i.val + n.val by omega, ← hbv,
        show z1.val.slice (2 * i.val + 2) (i.val + n.val) = s1.val by rw [hs1, hi9, hi10, hi4]] at hW
      have hS2 := wordsNat_set (back s3).val (i.val + n.val) (UScalar.cast .U64 rest) (by omega)
      rw [← hz3v, hb0, cast_u64_val] at hS2
      have hS3 := wordsNat_set z3.val (i.val + n.val + 1) (UScalar.cast .U64 rh) (by omega)
      rw [← hs4v, hz30, cast_u64_val] at hS3
      have hrestb : rest.val < 2 ^ 128 := by have := rest.hBounds; simpa using this
      have hrhv : rh.val % 2 ^ 64 = rest.val / 2 ^ 64 := by
        rw [hrh]; simp [Nat.shiftRight_eq_div_pow]; omega
      rw [hrhv] at hS3
      have hrmd := Nat.mod_add_div rest.val (2 ^ 64)
      have hsmd := Nat.mod_add_div sv.val (2 ^ 64)
      have hW1 := wordsNat_drop_succ x.val (i.val + 1) (by omega)
      rw [hs2, hi11] at hs3
      have hoff : offSum x.val (2 * (it.start.val + 1)) = offSum x.val i.val +
          x.val[i.val]!.val * 2 ^ (64 * (2 * i.val + 1)) * wordsNat (x.val.drop (i.val + 1)) +
          x.val[i.val + 1]!.val * 2 ^ (64 * (2 * (i.val + 1) + 1)) * wordsNat (x.val.drop (i.val + 1 + 1)) := by
        rw [show 2 * (it.start.val + 1) = i.val + 1 + 1 by omega, offSum, offSum]
      refine ⟨by rw [hend1, he], by omega, ?_, ?_, ?_, by omega⟩
      · simp only [Slice.length]; rw [hs4v, List.length_set]; exact hz3L
      · intro q hq
        rw [hs4v, getElem!_set_ne' _ _ _ _ (by omega), hz3v, getElem!_set_ne' _ _ _ _ (by omega), hbv,
          List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hs3L]; omega), hz1v, getElem!_set_ne' _ _ _ _ (by omega)]
        exact hz _ (by omega)
      · rw [hst, hoff, ← hxi', ← hxi1v]
        rw [← hiv] at hv
        rw [hxi1''] at hs3
        rw [← hxi1v] at hW1
        rw [hcv] at hs3
        have e1 : (2 : Nat) ^ (64 * (2 * i.val + 2)) = 2 ^ (64 * (2 * i.val + 1)) * 2 ^ 64 := by
          rw [show 64 * (2 * i.val + 2) = 64 * (2 * i.val + 1) + 64 by ring, pow_add]
        have e2 : (2 : Nat) ^ (64 * (i.val + n.val)) = 2 ^ (64 * (2 * i.val + 1)) * 2 ^ 64 * 2 ^ (64 * L) := by
          rw [show 64 * (i.val + n.val) = 64 * (2 * i.val + 1) + 64 + 64 * L by omega, pow_add, pow_add]
        have e3 : (2 : Nat) ^ (64 * (i.val + n.val + 1)) =
            2 ^ (64 * (2 * i.val + 1)) * 2 ^ 64 * 2 ^ (64 * L) * 2 ^ 64 := by
          rw [show 64 * (i.val + n.val + 1) = 64 * (2 * i.val + 1) + 64 + 64 * L + 64 by omega, pow_add, pow_add,
            pow_add]
        have e4 : (2 : Nat) ^ (64 * (2 * (i.val + 1) + 1)) = 2 ^ (64 * (2 * i.val + 1)) * 2 ^ 64 * 2 ^ 64 := by
          rw [show 64 * (2 * (i.val + 1) + 1) = 64 * (2 * i.val + 1) + 64 + 64 by ring, pow_add, pow_add]
        rw [e1] at hW; rw [e2] at hS2; rw [e3] at hS3; rw [e4]
        zify at hS1 hW hS2 hS3 hrmd hsmd hW1 hs3 hsv hv ⊢
        linear_combination hS3 + hS2 + (2 ^ (64 * (2 * i.val + 1)) * 2 ^ 64 * 2 ^ (64 * L) : Int) * hrmd + hW +
          (2 ^ (64 * (2 * i.val + 1)) * 2 ^ 64 : Int) * hs3 + hS1 + (2 ^ (64 * (2 * i.val + 1)) : Int) * hsmd +
          (2 ^ (64 * (2 * i.val + 1)) : Int) * hsv - (xi.val * 2 ^ (64 * (2 * i.val + 1)) : Int) * hW1 + hv
  · exact ⟨hend, hi, hzl, hzero, hval⟩

theorem sqr_limbs_loop1_spec (z0 : Slice U64) (iter : core.ops.range.Range Usize) (z : Slice U64) (out : U64)
    (hend : iter.end.val = z0.length) (hi : iter.start.val ≤ z0.length) (hzl : z.length = z0.length)
    (ho : out.val ≤ 1) (hdrop : z.val.drop iter.start.val = z0.val.drop iter.start.val)
    (hinv : wordsNat (z.val.take iter.start.val) + 2 ^ (64 * iter.start.val) * out.val =
      2 * wordsNat (z0.val.take iter.start.val)) :
    low.generic.limb64.mont.sqr_limbs_loop1 iter z out ⦃ r =>
      r.length = z0.length ∧ ∃ o : Nat, o ≤ 1 ∧ wordsNat r.val + 2 ^ (64 * z0.length) * o = 2 * wordsNat z0.val ⦄ := by
  unfold low.generic.limb64.mont.sqr_limbs_loop1
  apply loop.spec_decr_nat (fun x' => z0.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U64 =>
      x'.1.end.val = z0.length ∧ x'.1.start.val ≤ z0.length ∧ x'.2.1.length = z0.length ∧ x'.2.2.val ≤ 1 ∧
      x'.2.1.val.drop x'.1.start.val = z0.val.drop x'.1.start.val ∧
      wordsNat (x'.2.1.val.take x'.1.start.val) + 2 ^ (64 * x'.1.start.val) * x'.2.2.val =
        2 * wordsNat (z0.val.take x'.1.start.val))
  · rintro ⟨it, w, o⟩ ⟨he, hs, hwl, ho, hd, hv⟩
    simp only at he hs hwl ho hd hv
    unfold low.generic.limb64.mont.sqr_limbs_loop1.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = z0.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwL : w.val.length = z0.length := hwl
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp)] at hv
      exact ⟨hwl, o.val, ho, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      step as ⟨zi, hzi⟩
      step as ⟨i2, hi2⟩
      step as ⟨nx, hnx⟩
      step as ⟨i3, hi3⟩
      simp only [lift, bind_ok]
      step as ⟨w1, hw1⟩
      have hzi0 : zi = z0.val[it.start.val]! := by rw [hzi, ← getElem!_pos]; exact getElem!_of_drop_eq hd
      have hzb : zi.val < 2 ^ 64 := u64_lt zi
      have hnxv : nx.val = zi.val / 2 ^ 63 := by
        rw [hnx, hi2]; simp [Nat.shiftRight_eq_div_pow]
      have hi3v : i3.val = zi.val * 2 % 2 ^ 64 := by
        rw [hi3]; simp [Nat.shiftLeft_eq, u64_size]
      have hev : i3.val = 2 ^ 1 * (i3.val / 2) := by omega
      have horv : (i3 ||| o).val = i3.val + o.val := by
        rw [UScalar.val_or, hev, ← Nat.two_pow_add_eq_or_of_lt (by omega : o.val < 2 ^ 1)]
      have hkey : (i3 ||| o).val + 2 ^ 64 * nx.val = 2 * zi.val + o.val := by
        rw [horv, hi3v, hnxv]; omega
      have hw1v : w1.val = w.val.set it.start.val (i3 ||| o) := by rw [hw1]; simp
      refine ⟨by rw [hend1, he], by omega, by rw [hw1]; simp at hwl ⊢; omega,
        by rw [hnxv]; omega, ?_, ?_, by omega⟩
      · rw [hst, hw1v, drop_set_succ']
        rw [List.drop_eq_getElem_cons (show it.start.val < w.val.length by omega),
          List.drop_eq_getElem_cons (show it.start.val < z0.val.length by omega)] at hd
        exact (List.cons.inj hd).2
      · rw [hst, hw1v, take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_cons, wordsNat_nil,
          List.length_take, Nat.min_eq_left (by omega), wordsNat_take_succ' _ _ (by omega), ← hzi0]
        rw [show 64 * (it.start.val + 1) = 64 * it.start.val + 64 by ring, pow_add]
        zify at hv hkey ⊢
        linear_combination hv + (2 ^ (64 * it.start.val) : Int) * hkey
  · exact ⟨hend, hi, hzl, ho, hdrop, hinv⟩

/-- The squares of `x`'s first `r` limbs, `x[k]^2` at `2^(128k)`. -/
def diagSum (x : List U64) : Nat → Nat
  | 0 => 0
  | r + 1 => diagSum x r + x[r]!.val * x[r]!.val * 2 ^ (64 * (2 * r))

theorem sqr_limbs_loop2_spec (x z0 : Slice U64) (hzl0 : z0.length = 2 * x.length)
    (iter : core.ops.range.Range Usize) (z : Slice U64) (carry : U128)
    (hend : iter.end.val = x.length) (hi : iter.start.val ≤ x.length) (hzl : z.length = z0.length)
    (hc : carry.val ≤ 1) (hdrop : z.val.drop (2 * iter.start.val) = z0.val.drop (2 * iter.start.val))
    (hinv : wordsNat (z.val.take (2 * iter.start.val)) + 2 ^ (64 * (2 * iter.start.val)) * carry.val =
      wordsNat (z0.val.take (2 * iter.start.val)) + diagSum x.val iter.start.val) :
    low.generic.limb64.mont.sqr_limbs_loop2 iter x z carry ⦃ r =>
      r.length = z0.length ∧ ∃ c : Nat, c ≤ 1 ∧
        wordsNat r.val + 2 ^ (64 * z0.length) * c = wordsNat z0.val + diagSum x.val x.length ⦄ := by
  unfold low.generic.limb64.mont.sqr_limbs_loop2
  apply loop.spec_decr_nat (fun x' => x.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 × U128 =>
      x'.1.end.val = x.length ∧ x'.1.start.val ≤ x.length ∧ x'.2.1.length = z0.length ∧ x'.2.2.val ≤ 1 ∧
      x'.2.1.val.drop (2 * x'.1.start.val) = z0.val.drop (2 * x'.1.start.val) ∧
      wordsNat (x'.2.1.val.take (2 * x'.1.start.val)) + 2 ^ (64 * (2 * x'.1.start.val)) * x'.2.2.val =
        wordsNat (z0.val.take (2 * x'.1.start.val)) + diagSum x.val x'.1.start.val)
  · rintro ⟨it, w, cy⟩ ⟨he, hs, hwl, hc, hd, hv⟩
    simp only at he hs hwl hc hd hv
    unfold low.generic.limb64.mont.sqr_limbs_loop2.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = x.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      rw [← hzl0, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hv
      exact ⟨hwl, cy.val, hc, hv⟩
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      have hwL : w.val.length = z0.length := hwl
      have hz0L : z0.val.length = z0.length := rfl
      have hxL : x.val.length = x.length := rfl
      have hwmax : w.length ≤ Usize.max := w.property
      step as ⟨xi, hxi⟩
      step as ⟨i2, hi2⟩
      step as ⟨a, ha⟩
      step with mul_add_limb_spec xi xi a cy (by omega) as ⟨sv, hsv⟩
      simp only [lift, bind_ok]
      step as ⟨z1, hz1⟩
      step as ⟨i5, hi5⟩
      step as ⟨b, hb⟩
      step as ⟨i8, hi8, _⟩
      step as ⟨i9, hi9⟩
      step as ⟨w2, hw2⟩
      step as ⟨c1, hc1, _⟩
      set k := it.start.val with hk
      have hi2v : i2.val = 2 * k := hi2
      have hxi' : xi = x.val[k]! := by rw [hxi, ← getElem!_pos]
      have ha0 : a = z0.val[2 * k]! := by
        rw [ha, ← getElem!_pos, hi2v]; exact getElem!_of_drop_eq hd
      have hz1v : z1.val = w.val.set (2 * k) (UScalar.cast .U64 sv) := by rw [hz1]; simp [hi2v]
      have hb0 : b = z0.val[2 * k + 1]! := by
        rw [hb, ← getElem!_pos, hi5, hi2v, hz1v, getElem!_set_ne' _ _ _ _ (by omega),
          ← getElem!_drop', ← getElem!_drop' z0.val, hd]
      set sum := core.num.U128.wrapping_add (core.convert.num.FromU128U64.from b) i8 with hsumdef
      have hxb := u64_lt xi
      have hab := u64_lt a
      have hbb := u64_lt b
      have hsq : xi.val * xi.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      have hi8v : i8.val = sv.val / 2 ^ 64 := by rw [hi8]; simp [Nat.shiftRight_eq_div_pow]
      have hi8b : i8.val < 2 ^ 64 := by rw [hi8v, hsv]; omega
      have hsumv : sum.val = b.val + sv.val / 2 ^ 64 := by
        rw [hsumdef, core.num.U128.wrapping_add_val_eq, from_u128_val, hi8v]
        simp only [UScalar.size, UScalarTy.numBits]
        rw [Nat.mod_eq_of_lt (by omega)]
      have hc1v : c1.val = sum.val / 2 ^ 64 := by rw [hc1]; simp [Nat.shiftRight_eq_div_pow]
      have hw2v : w2.val = (w.val.set (2 * k) (UScalar.cast .U64 sv)).set (2 * k + 1) (UScalar.cast .U64 sum) := by
        rw [hw2]; simp [hi9, hi2v, hz1v]
      have hsmd := Nat.mod_add_div sv.val (2 ^ 64)
      have hsumd := Nat.mod_add_div sum.val (2 ^ 64)
      have hsvb : sv.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) + 1 := by rw [hsv]; omega
      have hsvd : sv.val / 2 ^ 64 ≤ 2 ^ 64 - 1 := by omega
      have hc1b : c1.val ≤ 1 := by rw [hc1v, hsumv]; omega
      refine ⟨by rw [hend1, he], by omega, by simp only [Slice.length]; rw [hw2v]; simp [hwL], hc1b, ?_, ?_,
        by omega⟩
      · rw [hst, hw2v, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, drop_set_succ',
          List.drop_set_of_lt (by omega)]
        rw [List.drop_eq_getElem_cons (show 2 * k < w.val.length by omega),
          List.drop_eq_getElem_cons (show 2 * k < z0.val.length by omega)] at hd
        have hd2 := (List.cons.inj hd).2
        rw [List.drop_eq_getElem_cons (show 2 * k + 1 < w.val.length by omega),
          List.drop_eq_getElem_cons (show 2 * k + 1 < z0.val.length by omega)] at hd2
        exact (List.cons.inj hd2).2
      · rw [hst, hw2v, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, take_set_succ' _ _ _ (by simp; omega),
          take_set_succ' _ _ _ (by omega), wordsNat_append, wordsNat_append, wordsNat_cons, wordsNat_nil,
          wordsNat_cons, wordsNat_nil, List.length_append, List.length_take, Nat.min_eq_left (by omega),
          wordsNat_take_succ' _ _ (by omega), wordsNat_take_succ' _ _ (by omega), cast_u64_val, cast_u64_val,
          diagSum, ← hxi', ← ha0, ← hb0]
        simp only [List.length_singleton]
        rw [show 64 * (2 * k + 1 + 1) = 64 * (2 * k) + 64 + 64 by ring,
          show 64 * (2 * k + 1) = 64 * (2 * k) + 64 by ring, pow_add, pow_add] at *
        rw [hc1v]
        zify at hv hsmd hsumd hsumv hsv ⊢
        linear_combination hv + (2 ^ (64 * (2 * k)) * 2 ^ 64 : Int) * hsumd +
          (2 ^ (64 * (2 * k)) * 2 ^ 64 : Int) * hsumv + (2 ^ (64 * (2 * k)) : Int) * hsmd +
          (2 ^ (64 * (2 * k)) : Int) * hsv
  · exact ⟨hend, hi, hzl, hc, hdrop, hinv⟩

theorem offSum_succ_end (x : List U64) : offSum x (x.length) = offSum x (2 * (x.length / 2)) := by
  rcases Nat.mod_two_eq_zero_or_one x.length with h | h
  · rw [show 2 * (x.length / 2) = x.length by omega]
  · obtain ⟨m, hm⟩ : ∃ m, x.length = m + 1 := ⟨x.length - 1, by omega⟩
    rw [hm, offSum, show 2 * ((m + 1) / 2) = m by omega, ← hm, List.drop_of_length_le (by omega), wordsNat_nil]
    simp

/-- A square is its diagonal plus twice its products of two different limbs. -/
theorem sq_eq_diag_off (x : List U64) :
    wordsNat x * wordsNat x = diagSum x x.length + 2 * offSum x x.length := by
  have key : ∀ r ≤ x.length, wordsNat (x.take r) * wordsNat (x.take r) +
      2 * wordsNat (x.take r) * 2 ^ (64 * r) * wordsNat (x.drop r) = diagSum x r + 2 * offSum x r := by
    intro r
    induction r with
    | zero => intro _; simp [wordsNat_nil, diagSum, offSum]
    | succ r ih =>
      intro hr
      have ih' := ih (by omega)
      rw [wordsNat_take_succ' _ _ (by omega), diagSum, offSum]
      rw [wordsNat_drop_succ _ _ (by omega)] at ih'
      rw [show 64 * (r + 1) = 64 * r + 64 by ring, show 64 * (2 * r + 1) = 64 * r + 64 * r + 64 by ring,
        show 64 * (2 * r) = 64 * r + 64 * r by ring, pow_add, pow_add, pow_add]
      linear_combination ih'
  have := key x.length le_rfl
  rw [List.take_of_length_le le_rfl, List.drop_of_length_le le_rfl, wordsNat_nil] at this
  simpa using this

/-- The scratch `sqr_limbs` takes at `n` limbs: a Karatsuba split at
`h = ceil(n / 2)` takes `3h` and its halves' scratch. -/
def sqrNeed (n : Nat) : Nat := if n < 64 then 0 else 3 * ((n + 1) / 2) + sqrNeed ((n + 1) / 2)
termination_by n
decreasing_by omega

theorem sqrNeed_mono (b : Nat) : ∀ a ≤ b, sqrNeed a ≤ sqrNeed b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rw [sqrNeed.eq_1 a, sqrNeed.eq_1 b]
    split <;> split
    · omega
    · omega
    · omega
    · have := ih ((b + 1) / 2) (by omega) ((a + 1) / 2) (by omega); omega

theorem karatsuba_sqr_eq : low.generic.limb64.mont.KARATSUBA_SQR = 64#usize := by
  unfold low.generic.limb64.mont.KARATSUBA_SQR; rfl

set_option maxHeartbeats 1000000 in
/-- `sqr_limbs`: `z := x^2` for `x` of `n` limbs, `z` of `2n`, and the
scratch Karatsuba takes from `KARATSUBA_SQR` limbs. -/
theorem sqr_limbs_spec (n : Nat) : ∀ (z x scratch : Slice U64), x.length = n →
    z.length = 2 * n → sqrNeed n ≤ scratch.length → 4 * n ≤ Usize.max →
    low.generic.limb64.mont.sqr_limbs z x scratch ⦃ r =>
      r.1.length = 2 * n ∧ r.2.length = scratch.length ∧ wordsNat r.1.val = wordsNat x.val * wordsNat x.val ⦄ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z x scratch hx hz hs hmax
  have hxL : x.val.length = n := hx
  have hzL : z.val.length = 2 * n := hz
  rw [low.generic.limb64.mont.sqr_limbs]
  have hlen : (Slice.len x).val = n := by simp only [Slice.len_val]; exact hx
  step as ⟨i, hi⟩
  step as ⟨z1, back, hz1, hz1l, hback⟩
  rw [karatsuba_sqr_eq]
  split
  · rename_i hn
    have hn' : n < 64 := by rw [← hlen]; simpa using hn
    clear ih
    have hiv : i.val = 2 * n := by rw [hi, hlen]
    step as ⟨z2, hz2l, hz2⟩
    step as ⟨i1, hi1⟩
    step with sqr_limbs_loop0_spec x (Slice.len x) (by rw [hlen]; exact hx)
      { start := 0#usize, «end» := i1 } z2 (by simp [hi1]) (by simp) (by rw [hz2l, hz1l, hiv, hlen])
      (by intro j _; rw [hz2]; by_cases hj : j < z1.length <;> simp [hj])
      (by rw [hz2, wordsNat_replicate_zero]; simp [offSum]) as ⟨z3, hz3l, hz3⟩
    rw [hlen, ← hxL, ← offSum_succ_end, hxL] at hz3
    rw [hlen] at hz3l
    step as ⟨i2, hi2⟩
    step with sqr_limbs_loop1_spec z3 { start := 0#usize, «end» := i2 } z3 0#u64
      (by simp [hi2, hlen, hz3l]) (by simp) rfl (by simp) rfl (by simp [wordsNat_nil]) as ⟨z4, hz4l, o, ho, hz4⟩
    step with sqr_limbs_loop2_spec x z4 (by rw [hz4l, hz3l, hx]) { start := 0#usize, «end» := Slice.len x } z4 0#u128
      (by simp [hlen, hx]) (by simp) rfl (by simp) rfl (by simp [wordsNat_nil, diagSum]) as ⟨z5, hz5l, c, hc, hz5⟩
    have hsq := sq_eq_diag_off x.val
    rw [hxL] at hsq
    rw [hz3l] at hz4
    rw [hz4l, hz3l, hx] at hz5
    have hX := wordsNat_lt' x.val
    rw [hxL] at hX
    have hXX : wordsNat x.val * wordsNat x.val < 2 ^ (64 * (2 * n)) := by
      rw [show 64 * (2 * n) = 64 * n + 64 * n by ring, pow_add]; exact Nat.mul_lt_mul'' hX hX
    have ho0 : o = 0 := by
      by_contra h0
      have : 2 ^ (64 * (2 * n)) ≤ 2 ^ (64 * (2 * n)) * o := Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [ho0] at hz4
    have hc0 : c = 0 := by
      by_contra h0
      have : 2 ^ (64 * (2 * n)) ≤ 2 ^ (64 * (2 * n)) * c := Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [hc0] at hz5
    have hz5L : z5.val.length = 2 * n := by rw [show z5.val.length = z5.length from rfl, hz5l, hz4l, hz3l]
    have hb := hback z5
    rw [setSlice_zero_full _ _ (by rw [hz5L, hzL])] at hb
    refine ⟨by simp only [Slice.length]; rw [hb, hz5L], ?_⟩
    rw [hb]; omega
  · rename_i hn
    have hn' : 64 ≤ n := by rw [← hlen]; simpa using hn
    have hdc : core.num.Usize.div_ceil (Slice.len x) 2#usize ⦃ r => r.val = (n + 1) / 2 ⦄ := by
      simp [core.num.Usize.div_ceil, WP.spec_ok, hlen]
    step with hdc as ⟨h, hh⟩
    have hneed : sqrNeed n = 3 * h.val + sqrNeed h.val := by
      rw [sqrNeed.eq_1, hh]; simp [show ¬ n < 64 by omega]
    have hzz : z1.length = 2 * n := by rw [hz1l, hi, hlen]
    step with core.slice.Slice.split_at_mut.spec scratch h (by omega) as ⟨dx, rest, smb, hdxl, hrestl, _, _, hsmb⟩
    step as ⟨i1, hi1⟩
    step with core.slice.Slice.split_at_mut.spec rest i1 (by omega) as ⟨d, rest1, smb1, hdl, hrest1l, _, _, hsmb1⟩
    step with core.slice.Slice.split_at.spec x h (by omega) as ⟨x0, x1, hx0l, hx1l, hx0, hx1⟩
    step with abs_diff_spec dx x0 x1 (by omega) (by omega) as ⟨sx, dx1, hdx1l, hsx, hdx1⟩
    step with ih h.val (by omega) d dx1 rest1 (by omega) (by omega) (by omega) (by omega)
      as ⟨d1, rest2, hd1l, hrest2l, hd1⟩
    step with core.slice.Slice.split_at_mut.spec z1 i1 (by omega) as ⟨z0, z2, smb2, hz0l, hz2l, hz0, hz2, hsmb2⟩
    step with ih h.val (by omega) z0 x0 rest2 (by omega) (by omega) (by omega) (by omega)
      as ⟨z01, rest3, hz01l, hrest3l, hz01⟩
    have hx1n : x1.length = n - h.val := by rw [hx1l, hx]
    have hz2n : z2.length = 2 * (n - h.val) := by rw [hz2l, hzz, hi1]; omega
    have hr3 : sqrNeed (n - h.val) ≤ rest3.length := by
      have h1 := sqrNeed_mono h.val (n - h.val) (by omega)
      have h2 : sqrNeed h.val ≤ rest3.length := by omega
      exact le_trans h1 h2
    have hm4 : 4 * (n - h.val) ≤ Usize.max := by omega
    step with ih (n - h.val) (by omega) z2 x1 rest3 hx1n hz2n hr3 hm4
      as ⟨z21, rest4, hz21l, hrest4l, hz21⟩
    obtain ⟨hz3v, hz3l⟩ := hsmb2 z01 z21 (by omega) (by omega)
    have hX : wordsNat x.val = wordsNat x0.val + 2 ^ (64 * h.val) * wordsNat x1.val := by
      conv_lhs => rw [← List.take_append_drop h.val x.val]
      rw [wordsNat_append, List.length_take, Nat.min_eq_left (by omega), hx0, hx1]
    have hz3L : (smb2 (z01, z21)).length = 2 * n := by rw [hz3l, hzz]
    have hz01L : z01.val.length = 2 * h.val := hz01l
    have hM : ((2 * wordsNat x0.val * wordsNat x1.val : Nat) : Int) = wordsNat z01.val + wordsNat z21.val +
        (if (1#u64).val = 0 then (wordsNat d1.val : Int) else -(wordsNat d1.val : Int)) := by
      simp only [show (1#u64).val ≠ 0 by simp, ↓reduceIte]
      rw [hz01, hz21, hd1, hdx1]
      split
      · rename_i hlt
        push_cast [Nat.cast_sub hlt.le]; ring
      · rename_i hlt
        push_cast [Nat.cast_sub (not_lt.mp hlt)]; ring
    have hprod : wordsNat z01.val + 2 ^ (64 * (2 * h.val)) * wordsNat z21.val +
        2 ^ (64 * h.val) * (2 * wordsNat x0.val * wordsNat x1.val) = wordsNat x.val * wordsNat x.val := by
      rw [hz01, hz21, hX, show 64 * (2 * h.val) = 64 * h.val + 64 * h.val by ring, pow_add]; ring
    have hXX : wordsNat x.val * wordsNat x.val < 2 ^ (64 * (2 * n)) := by
      have hx' := wordsNat_lt' x.val
      rw [hxL] at hx'
      rw [show 64 * (2 * n) = 64 * n + 64 * n by ring, pow_add]
      exact Nat.mul_lt_mul'' hx' hx'
    step with add_middle_spec (smb2 (z01, z21)) d1 h 1#u64 (by simp) hd1l (by omega) (by omega) (by omega)
      (2 * wordsNat x0.val * wordsNat x1.val)
      (by rw [hz3v, ← hz01L, List.take_left, List.drop_left]; exact hM)
      (by rw [hz3v, wordsNat_append, hz01L, hz3L]; omega) as ⟨z4, d2, hz4l, hd2l, hz4⟩
    have hz4L : z4.val.length = 2 * n := by rw [show z4.val.length = z4.length from rfl, hz4l, hz3L]
    have hb := hback z4
    rw [setSlice_zero_full _ _ (by rw [hz4L, hzL])] at hb
    have hr5 := (hsmb1 d2 rest4 (by omega) (by omega)).2
    have hr6 := (hsmb dx1 (smb1 (d2, rest4)) (by omega) (by omega)).2
    refine ⟨by simp only [Slice.length]; rw [hb, hz4L], hr6, ?_⟩
    rw [hb, hz4, hz3v, wordsNat_append, hz01L, ← hprod]

/-! ## CIOS: `mont_mul_limbs` -/

theorem getElem!_set_self' {α : Type} [Inhabited α] (l : List α) (i : Nat) (v : α) (h : i < l.length) :
    (l.set i v)[i]! = v := by
  simp [h]

/-- The carries of a CIOS step fit where it puts them. -/
theorem cios_carries (tn c c2 : Nat) (htn : tn < 2 ^ 64) (hc : c < 2 ^ 64) (hc2 : c2 < 2 ^ 64) :
    tn + c < 2 ^ 128 ∧ (tn + c) % 2 ^ 64 + c2 < 2 ^ 128 ∧ (tn + c) / 2 ^ 64 < 2 ^ 64 ∧
      ((tn + c) % 2 ^ 64 + c2) / 2 ^ 64 < 2 ^ 64 ∧
      (tn + c) / 2 ^ 64 % 2 ^ 64 + ((tn + c) % 2 ^ 64 + c2) / 2 ^ 64 % 2 ^ 64 < 2 ^ 64 := by
  omega

theorem cios_take (t : List U64) (k : Nat) (hk : 1 ≤ k) (hL : t.length = k + 2) (a b : U64) :
    wordsNat (((t.set (k - 1) a).set k b).take (k + 1)) =
      wordsNat (t.take (k - 1)) + 2 ^ (64 * (k - 1)) * a.val + 2 ^ (64 * k) * b.val := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [take_set_succ' _ _ _ (by rw [List.length_set]; omega), take_set_succ' _ _ _ (by omega), wordsNat_append,
    wordsNat_append, wordsNat_cons, wordsNat_nil, wordsNat_cons, wordsNat_nil, List.length_append, List.length_take,
    Nat.min_eq_left (by omega), List.length_singleton]
  ring

theorem cios_bound {V V' X Y M u : Nat} (hV : V < 2 * M) (hx : X < 2 ^ 64) (hu : u < 2 ^ 64) (hY : Y < M)
    (h : 2 ^ 64 * V' = V + X * Y + u * M) : V' < 2 * M := by
  have h1 : X * Y ≤ (2 ^ 64 - 1) * M := Nat.mul_le_mul (by omega) hY.le
  have h2 : u * M ≤ (2 ^ 64 - 1) * M := Nat.mul_le_mul (by omega) le_rfl
  omega

theorem cios_inv {i V V' Xi xi Y Q u M : Nat} (hQ : Q < 2 ^ (64 * i)) (hu : u < 2 ^ 64)
    (hVQ : 2 ^ (64 * i) * V = Xi * Y + Q * M) (h : 2 ^ 64 * V' = V + xi * Y + u * M) :
    Q + 2 ^ (64 * i) * u < 2 ^ (64 * (i + 1)) ∧
      2 ^ (64 * (i + 1)) * V' = (Xi + 2 ^ (64 * i) * xi) * Y + (Q + 2 ^ (64 * i) * u) * M := by
  rw [show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
  constructor
  · have : 2 ^ (64 * i) * u ≤ 2 ^ (64 * i) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : 2 ^ (64 * i) * (2 ^ 64 - 1) + 2 ^ (64 * i) = 2 ^ (64 * i) * 2 ^ 64 := by
      rw [← Nat.mul_succ]; congr 1
    omega
  · rw [mul_assoc, h]; zify at hVQ ⊢; linear_combination hVQ

theorem pow_pred64 (k : Nat) (hk : 1 ≤ k) : (2 : Nat) ^ (64 * k) = 2 ^ (64 * (k - 1)) * 2 ^ 64 := by
  rw [← pow_add]; congr 1; omega

/-- The limb `add_shift` drops is zero for `u = t[0] n0`. -/
theorem low_zero (a n0 m0 : Nat) (h : (m0 * n0 + 1) % 2 ^ 64 = 0) :
    (a * n0 % 2 ^ 64 * m0 + a) % 2 ^ 64 = 0 := by
  have h1 : (a * n0 % 2 ^ 64 * m0 + a) % 2 ^ 64 = (a * (m0 * n0 + 1)) % 2 ^ 64 := by
    rw [show a * (m0 * n0 + 1) = a * n0 * m0 + a by ring]
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
  rw [h1, Nat.mul_mod, h, mul_zero, Nat.zero_mod]

/-- CIOS's state after `i` steps: `t`'s low `k + 1` limbs hold `V < 2m` with
`2^(64i) V = x[..i] y + Q m`. -/
def CiosInv (x : List U64) (Y M k i : Nat) (t : List U64) : Prop :=
  t.length = k + 2 ∧ wordsNat (t.take (k + 1)) < 2 * M ∧
    ∃ Q, Q < 2 ^ (64 * i) ∧ 2 ^ (64 * i) * wordsNat (t.take (k + 1)) = wordsNat (x.take i) * Y + Q * M

set_option maxHeartbeats 2000000 in
theorem mont_mul_limbs_loop_spec (x y m : Slice U64) (n0 : U64) (n : Usize) (hn : n.val = m.length)
    (hx : x.length = m.length) (hy : y.length = m.length) (hk1 : 1 ≤ m.length) (hmax : m.length + 2 ≤ Usize.max)
    (hY : wordsNat y.val < wordsNat m.val) (hn0 : (m.val[0]!.val * n0.val + 1) % 2 ^ 64 = 0)
    (iter : core.ops.range.Range Usize) (t : Slice U64)
    (hend : iter.end.val = m.length) (hi : iter.start.val ≤ m.length)
    (hinv : CiosInv x.val (wordsNat y.val) (wordsNat m.val) m.length iter.start.val t.val) :
    low.generic.limb64.mont.mont_mul_limbs_loop iter t x y m n0 n ⦃ r =>
      CiosInv x.val (wordsNat y.val) (wordsNat m.val) m.length m.length r.val ⦄ := by
  unfold low.generic.limb64.mont.mont_mul_limbs_loop
  apply loop.spec_decr_nat (fun x' => m.length - x'.1.start.val)
    (fun x' : core.ops.range.Range Usize × Slice U64 =>
      x'.1.end.val = m.length ∧ x'.1.start.val ≤ m.length ∧
      CiosInv x.val (wordsNat y.val) (wordsNat m.val) m.length x'.1.start.val x'.2.val)
  · rintro ⟨it, w⟩ ⟨he, hs, hv⟩
    simp only at he hs hv
    unfold low.generic.limb64.mont.mont_mul_limbs_loop.body
    step as ⟨op, iter1, hop, hend1⟩
    cases op with
    | none =>
      have h0 : it.start.val = m.length := by
        split at hop
        · simp at hop
        · scalar_tac
      simp only [WP.spec_ok]
      rw [h0] at hv
      exact hv
    | some j =>
      have hlt : it.start.val < it.end.val := by
        by_contra hc; simp [hc] at hop
      simp only [hlt, ↓reduceIte, Option.some.injEq] at hop
      obtain ⟨rfl, hst⟩ := hop
      rw [he] at hlt
      obtain ⟨hwl, hV, Q, hQ, hVQ⟩ := hv
      have hmL : m.val.length = m.length := rfl
      have hxL : x.val.length = m.length := hx
      have hyL : y.val.length = m.length := hy
      have hwL : w.val.length = m.length + 2 := hwl
      have hwmax : w.length ≤ Usize.max := w.property
      step as ⟨tn, htn⟩
      simp only [lift, bind_ok]
      step as ⟨s, back, hsw, hsl, hback⟩
      step as ⟨xi, hxi⟩
      step with mul_add_spec s y xi (by simp only [Slice.length] at hsl ⊢; rw [hsl, hn]; exact hy) as ⟨c, s1, hs1l, hc, hs1⟩
      step as ⟨t2, ht2⟩
      step as ⟨sh, hsh, _⟩
      step as ⟨i7, hi7⟩
      step as ⟨t3, ht3⟩
      set k := m.length with hk
      have hnv : n.val = k := hn
      have hsv : s.val = w.val.take k := by rw [hsw, hnv]; simp [List.slice]
      have hsL : s.length = k := by rw [hsl, hnv]
      have hs1L : s1.val.length = k := by rw [show s1.val.length = s1.length from rfl, hs1l, hsL]
      rw [hsL, hsv] at hs1
      set sum := core.num.U128.wrapping_add (core.convert.num.FromU128U64.from tn) c with hsumdef
      have htn' : tn = w.val[k]! := by rw [htn, ← getElem!_pos, hnv]
      have hsumv : sum.val = tn.val + c.val := by
        rw [hsumdef, core.num.U128.wrapping_add_val_eq, from_u128_val]
        simp only [UScalar.size, UScalarTy.numBits]
        have := u64_lt tn
        rw [Nat.mod_eq_of_lt (by omega)]
      have hshv : sh.val = sum.val / 2 ^ 64 := by rw [hsh]; simp [Nat.shiftRight_eq_div_pow]
      have ht1v : (back s1).val = s1.val ++ w.val.drop k := by
        rw [hback, setSlice_eq _ _ _ (by omega)]; simp [hs1L]
      have ht3v : t3.val = ((s1.val ++ w.val.drop k).set k (UScalar.cast .U64 sum)).set (k + 1)
          (UScalar.cast .U64 sh) := by
        rw [ht3, ht2]; simp [hi7, hnv, ht1v]
      have ht3L : t3.val.length = k + 2 := by rw [ht3v]; simp [hs1L]; omega
      have ht3k : t3.val.take k = s1.val := by
        rw [ht3v, List.take_set_of_le (by omega), List.take_set_of_le (by omega), List.take_left' hs1L]
      have ht3a : t3.val[k]! = UScalar.cast .U64 sum := by
        rw [ht3v, getElem!_set_ne' _ _ _ _ (by omega), getElem!_set_self' _ _ _ (by simp [hs1L]; omega)]
      have ht3b : t3.val[k + 1]! = UScalar.cast .U64 sh := by
        rw [ht3v, getElem!_set_self' _ _ _ (by simp [hs1L]; omega)]
      have ht30' : t3.val[0]! = s1.val[0]! := by
        rw [← ht3k]; simp [List.getElem!_eq_getElem?_getD, show 0 < k by omega]
      step as ⟨t30, ht30⟩
      have ht30v : t30 = t3.val[0]! := by rw [ht30, ← getElem!_pos]
      set u := core.num.U64.wrapping_mul t30 n0 with hudef
      have huv : u.val = t30.val * n0.val % 2 ^ 64 := by
        rw [hudef, core.num.U64.wrapping_mul_val_eq]; simp only [UScalar.size, UScalarTy.numBits]
      have hlow : (u.val * m.val[0]!.val + t3.val[0]!.val) % 2 ^ 64 = 0 := by
        rw [huv, ← ht30v]; exact low_zero _ _ _ hn0
      step with add_shift_spec t3 m u hk1 (by simp only [Slice.length]; omega) as ⟨c2, t4, hc2, ht4l, ht4d, ht4⟩
      rw [hlow, add_zero, ht3k] at ht4
      have ht4L : t4.val.length = k + 2 := by rw [show t4.val.length = t4.length from rfl, ht4l]; exact ht3L
      have ht4a : t4.val[k]! = UScalar.cast .U64 sum := by
        rw [← ht3a, ← Nat.add_zero k, ← getElem!_drop', ht4d, getElem!_drop']
      have ht4b : t4.val[k + 1]! = UScalar.cast .U64 sh := by
        rw [← ht3b, ← getElem!_drop', ht4d, getElem!_drop']
      step as ⟨i10, hi10⟩
      step as ⟨i12, hi12⟩
      step as ⟨t5, ht5⟩
      step as ⟨i14, hi14⟩
      step as ⟨i15, hi15, _⟩
      step as ⟨s2, hs2⟩
      have hi10' : i10 = UScalar.cast .U64 sum := by rw [hi10, ← getElem!_pos, hnv, ht4a]
      set sum1 := core.num.U128.wrapping_add (core.convert.num.FromU128U64.from i10) c2 with hsum1def
      obtain ⟨hcar1, hcar2, hcar3, hcar4, hcar5⟩ := cios_carries tn.val c.val c2.val (u64_lt tn) hc hc2
      have hsumv : sum.val = tn.val + c.val := by
        rw [hsumdef, core.num.U128.wrapping_add_val_eq, from_u128_val]
        simp only [UScalar.size, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt hcar1
      have hsum1v : sum1.val = sum.val % 2 ^ 64 + c2.val := by
        rw [hsum1def, core.num.U128.wrapping_add_val_eq, from_u128_val, hi10', cast_u64_val]
        simp only [UScalar.size, UScalarTy.numBits]
        rw [hsumv]; exact Nat.mod_eq_of_lt hcar2
      have hi15v : i15.val = sum1.val / 2 ^ 64 := by rw [hi15]; simp [Nat.shiftRight_eq_div_pow]
      have hi12v : i12.val = k - 1 := by rw [hi12, hnv]
      have ht5v : t5.val = t4.val.set (k - 1) (UScalar.cast .U64 sum1) := by rw [ht5]; simp [hi12v]
      have hi14' : i14 = UScalar.cast .U64 sh := by
        rw [hi14, ← getElem!_pos, hi7, hnv, ht5v, getElem!_set_ne' _ _ _ _ (by omega), ht4b]
      set top := core.num.U64.wrapping_add i14 (UScalar.cast .U64 i15) with htopdef
      have htopv : top.val = sum.val / 2 ^ 64 + sum1.val / 2 ^ 64 := by
        rw [htopdef, core.num.U64.wrapping_add_val_eq, hi14', cast_u64_val, cast_u64_val, hi15v, hshv]
        simp only [UScalar.size, UScalarTy.numBits]
        rw [hsum1v, hsumv, Nat.mod_eq_of_lt hcar5, Nat.mod_eq_of_lt hcar3, Nat.mod_eq_of_lt hcar4]
      have hs2v : s2.val = (t4.val.set (k - 1) (UScalar.cast .U64 sum1)).set k top := by
        rw [hs2, ← ht5v]; simp [hnv]
      have hs2L : s2.val.length = k + 2 := by rw [hs2v, List.length_set, List.length_set]; exact ht4L
      -- The new value, `(V + x[i] y + u m) / 2^64`.
      have hV' : 2 ^ 64 * wordsNat (s2.val.take (k + 1)) =
          wordsNat (w.val.take (k + 1)) + xi.val * wordsNat y.val + u.val * wordsNat m.val := by
        rw [hs2v, cios_take _ _ hk1 ht4L, cast_u64_val,
          wordsNat_take_succ' _ _ (show k < w.val.length by rw [hwL]; exact Nat.lt_add_of_pos_right two_pos),
          ← htn', pow_pred64 k hk1]
        rw [pow_pred64 k hk1] at ht4 hs1
        have hsmd := Nat.mod_add_div sum.val (2 ^ 64)
        have hs1md := Nat.mod_add_div sum1.val (2 ^ 64)
        rw [htopv]
        zify at ht4 hs1 hsmd hs1md hsum1v hsumv ⊢
        linear_combination ht4 + hs1 + (2 ^ (64 * (k - 1)) * 2 ^ 64 : Int) * hsumv +
          (2 ^ (64 * (k - 1)) * 2 ^ 64 : Int) * hs1md + (2 ^ (64 * (k - 1)) * 2 ^ 64 : Int) * hsmd +
          (2 ^ (64 * (k - 1)) * 2 ^ 64 : Int) * hsum1v
      have hxi' : xi = x.val[it.start.val]! := by rw [hxi, ← getElem!_pos]
      obtain ⟨hQ', hVQ'⟩ := cios_inv hQ (u64_lt u) hVQ hV'
      rw [hxi', ← wordsNat_take_succ' _ _ (by omega)] at hVQ'
      refine ⟨by rw [hend1, he], by rw [hst]; exact Nat.succ_le_of_lt hlt, ?_,
        by rw [hst]; exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)⟩
      unfold CiosInv
      rw [hst]
      exact ⟨hs2L, cios_bound hV (u64_lt xi) (u64_lt u) hY hV', _, hQ', hVQ'⟩
  · exact ⟨hend, hi, hinv⟩

/-- A Montgomery product's last step: `V = R + 2^(64k) T` below `2m` less
`m` where `T` is set or `R` is not below `m` gives `V mod m`. -/
theorem cond_sub {R T M Bk r1 b bel : Nat} (hRlt : R < Bk) (hMk : M < Bk) (hr1 : r1 < Bk) (hT : T ≤ 1)
    (hX : R + Bk * T < 2 * M) (hb : b ≤ 1) (hbel : bel = if R < M then 1 else 0)
    (h : (r1 : Int) - Bk * b = R - (if T = 0 ∧ bel = 1 then 0 else M)) : r1 = (R + Bk * T) % M := by
  have hM0 : 0 < M := by omega
  rcases (show T = 0 ∨ T = 1 by omega) with ht | ht
  · subst ht
    simp only [mul_zero, add_zero] at hX ⊢
    by_cases hRM : R < M
    · have hb1 : bel = 1 := by rw [hbel]; simp [hRM]
      simp only [hb1, and_self, ↓reduceIte, Nat.cast_zero, sub_zero] at h
      rw [Nat.mod_eq_of_lt hRM]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> push_cast at h <;> omega
    · have hb0 : bel = 0 := by rw [hbel]; simp [hRM]
      simp only [hb0, zero_ne_one, and_false, ↓reduceIte] at h
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> push_cast at h <;> omega
  · subst ht
    simp only [one_ne_zero, false_and, ↓reduceIte] at h
    simp only [mul_one] at hX ⊢
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> push_cast at h <;> omega

/-- `mont_mul_limbs`: CIOS's `x·y·2^(-64k) mod m` in `t`'s low `k` limbs,
for `t` of `k + 2` zero limbs. -/
theorem mont_mul_limbs_spec (t x y m : Slice U64) (n0 : U64) (hk1 : 1 ≤ m.length)
    (hx : x.length = m.length) (hy : y.length = m.length) (ht : t.val = List.replicate (m.length + 2) 0#u64)
    (hmax : m.length + 2 ≤ Usize.max) (hY : wordsNat y.val < wordsNat m.val)
    (hn0 : (m.val[0]!.val * n0.val + 1) % 2 ^ 64 = 0) :
    low.generic.limb64.mont.mont_mul_limbs t x y m n0 ⦃ r =>
      r.length = m.length + 2 ∧ wordsNat (r.val.take m.length) < wordsNat m.val ∧
        wordsNat (r.val.take m.length) * 2 ^ (64 * m.length) % wordsNat m.val =
          wordsNat x.val * wordsNat y.val % wordsNat m.val ⦄ := by
  unfold low.generic.limb64.mont.mont_mul_limbs
  have hmL : m.val.length = m.length := rfl
  have hxL : x.val.length = m.length := hx
  have hM0 : 0 < wordsNat m.val := by omega
  step with mont_mul_limbs_loop_spec x y m n0 m.len (by simp) hx hy hk1 hmax hY hn0
    { start := 0#usize, «end» := m.len } t (by simp) (by simp)
    ⟨by simp [ht], by rw [ht, List.take_replicate, wordsNat_replicate_zero]; omega, 0, by simp,
      by simp [ht, List.take_replicate, wordsNat_replicate_zero, wordsNat_nil]⟩ as ⟨t1, hI⟩
  obtain ⟨ht1l, hV, Q, hQ, hVQ⟩ := hI
  rw [List.take_of_length_le (l := x.val) (by omega)] at hVQ
  have ht1L : t1.val.length = m.length + 2 := ht1l
  step as ⟨s, hs, hsl⟩
  have hsv : s.val = t1.val.take m.length := by rw [hs]; simp [List.slice]
  have hsL : s.length = m.length := by simp only [Slice.length]; rw [hsv, List.length_take]; omega
  step with cmp_lt_limbs_spec s m (by rw [hsL]) as ⟨below, hbelow⟩
  step as ⟨tk, htk⟩
  simp only [lift, bind_ok]
  step as ⟨s1, back, hs1, hs1l, hback⟩
  have hs1v : s1.val = t1.val.take m.length := by rw [hs1]; simp [List.slice]
  have hs1L : s1.length = m.length := by simp only [Slice.length]; rw [hs1v, List.length_take]; omega
  have htk' : tk = t1.val[m.length]! := by rw [htk, ← getElem!_pos]; simp
  set R := wordsNat (t1.val.take m.length) with hR
  set M := wordsNat m.val with hMdef
  have hRlt : R < 2 ^ (64 * m.length) := by
    have := wordsNat_lt' (t1.val.take m.length); rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  have hVsplit := wordsNat_take_succ' t1.val m.length (by omega)
  rw [← htk'] at hVsplit
  have hMk : M < 2 ^ (64 * m.length) := by have := wordsNat_lt' m.val; rwa [hmL] at this
  have htkb : tk.val ≤ 1 := by
    by_contra h
    have : 2 ^ (64 * m.length) * 2 ≤ 2 ^ (64 * m.length) * tk.val := Nat.mul_le_mul_left _ (by omega)
    omega
  have hbel : below.val ≤ 1 := by rw [hbelow]; split <;> simp
  have hbit : (tk ||| (below ^^^ 1#u64)).val ≤ 1 := by
    rw [or_not_val _ _ htkb hbel]; split <;> simp
  step with sub_limbs_masked_spec s1 m _ (neg_bit_mask _ hbit) (by rw [hs1L]) as ⟨r1, hr1l, b, hb, hr1⟩
  have hmasked : masked (core.num.U64.wrapping_sub 0#u64 (tk ||| (below ^^^ 1#u64))) M =
      if tk.val = 0 ∧ below.val = 1 then 0 else M := by
    unfold masked
    rw [neg_bit_val _ hbit, or_not_val _ _ htkb hbel]
    by_cases hc : tk.val = 0 ∧ below.val = 1 <;> simp [hc]
  rw [hmasked, hs1L, hs1v, ← hR] at hr1
  rw [hsv, ← hR] at hbelow
  have hr1L : r1.val.length = m.length := by simp only [Slice.length] at hr1l hs1L; omega
  have hr1lt : wordsNat r1.val < 2 ^ (64 * m.length) := by have := wordsNat_lt' r1.val; rwa [hr1L] at this
  have hR1 := cond_sub hRlt hMk hr1lt htkb (by rw [← hVsplit]; exact hV) hb hbelow hr1
  rw [← hVsplit] at hR1
  have hbv : (back r1).val = r1.val ++ t1.val.drop m.length := by
    rw [hback, setSlice_eq _ _ _ (by omega)]; simp [hr1L]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Slice.length]; rw [hbv, List.length_append, hr1L, List.length_drop]; omega
  · rw [hbv, List.take_left' hr1L, hR1]; exact Nat.mod_lt _ hM0
  · rw [hbv, List.take_left' hr1L, hR1, Nat.mod_mul_mod, mul_comm, hVQ, Nat.add_mul_mod_self_right]

/-! ## Scratch at RSA's widths -/

theorem mulNeed_small (k : Nat) (hk : k < 32) : mulNeed k = 0 := by rw [mulNeed.eq_1]; simp [hk]

theorem sqrNeed_small (k : Nat) (hk : k < 64) : sqrNeed k = 0 := by rw [sqrNeed.eq_1]; simp [hk]

/-- `MAX_LIMBS`'s Karatsuba scratch fits `SCRATCH`. -/
theorem mulNeed_le (k : Nat) (hk : k ≤ 128) : mulNeed k ≤ 576 := by
  have h : mulNeed 128 = 448 := by
    rw [mulNeed.eq_1]; norm_num; rw [mulNeed.eq_1]; norm_num; rw [mulNeed.eq_1]; norm_num
    rw [mulNeed_small 16 (by norm_num)]
  have := mulNeed_mono 128 k hk
  omega

theorem sqrNeed_le (k : Nat) (hk : k ≤ 128) : sqrNeed k ≤ 576 := by
  have h : sqrNeed 128 = 288 := by
    rw [sqrNeed.eq_1]; norm_num; rw [sqrNeed.eq_1]; norm_num
    rw [sqrNeed_small 32 (by norm_num)]
  have := sqrNeed_mono 128 k hk
  omega

/-! ## `join` and the reductions' entries -/

/-- `join`: `z := x[..z.len]`, for `x` at least as long. -/
theorem join_spec (x z : Slice U64) (h : z.length ≤ x.length) :
    low.generic.limb64.join x z ⦃ r => r.val = x.val.take z.length ⦄ := by
  unfold low.generic.limb64.join
  simp only [lift, bind_ok]
  have hn : (core.cmp.impls.OrdUsize.min x.len z.len).val = z.length := by
    rw [core.cmp.impls.OrdUsize.min_val]; simp; omega
  step as ⟨s, back, hs, hsl, hback⟩
  step as ⟨s1, hs1, hs1l⟩
  step with core.slice.Slice.copy_from_slice.step_spec _ s s1 (by rw [hsl, hs1l]) as ⟨s2, hs2⟩
  rw [hback, hs2, hs1, hn]
  have hzL : z.val.length = z.length := rfl
  rw [setSlice_zero_full _ _ (by simp [List.slice]; omega)]
  simp [List.slice]

/-- `mont_sqr_limbs`: `x^2·2^(-64k) mod m` in `t`'s top `k` limbs. -/
theorem mont_sqr_limbs_spec (t x m : Slice U64) (n0 : U64) (hk1 : 1 ≤ m.length) (hk : m.length ≤ 128)
    (hx : x.length = m.length) (ht : t.length = 2 * m.length) (hX : wordsNat x.val < wordsNat m.val)
    (hn0 : (wordsNat m.val * n0.val + 1) % 2 ^ 64 = 0) :
    low.generic.limb64.mont.mont_sqr_limbs t x m n0 ⦃ r =>
      r.length = 2 * m.length ∧ wordsNat (r.val.drop m.length) < wordsNat m.val ∧
        wordsNat (r.val.drop m.length) * 2 ^ (64 * m.length) % wordsNat m.val =
          wordsNat x.val * wordsNat x.val % wordsNat m.val ⦄ := by
  unfold low.generic.limb64.mont.mont_sqr_limbs
  have hmax : 4 * m.length ≤ Usize.max := by scalar_tac
  have hMk : wordsNat m.val < 2 ^ (64 * m.length) := wordsNat_lt' m.val
  have hT : wordsNat x.val * wordsNat x.val < 2 ^ (64 * (2 * m.length - m.length)) * wordsNat m.val := by
    rw [show 2 * m.length - m.length = m.length by omega]
    calc wordsNat x.val * wordsNat x.val < wordsNat m.val * wordsNat m.val := Nat.mul_lt_mul'' hX hX
      _ ≤ 2 ^ (64 * m.length) * wordsNat m.val := Nat.mul_le_mul_right _ hMk.le
  have hsq : ∀ s : Slice U64, sqrNeed x.length ≤ s.length →
      (do let (t2, _) ← low.generic.limb64.mont.sqr_limbs t x s; ok t2) ⦃ t1 =>
        t1.length = 2 * m.length ∧ wordsNat t1.val = wordsNat x.val * wordsNat x.val ⦄ := by
    intro s hs
    step with sqr_limbs_spec x.length t x s rfl (by omega) hs (by omega) as ⟨t2, s2, ht2l, _, ht2⟩
    exact ⟨by omega, ht2⟩
  have hbranch : (if Slice.len x < low.generic.limb64.mont.KARATSUBA_SQR then do
        let (s, _) ← lift (Array.to_slice_mut (Std.Array.empty U64))
        let (t2, _) ← low.generic.limb64.mont.sqr_limbs t x s
        ok t2
      else do
        let a := Array.repeat 576#usize 0#u64
        let (s, _) ← lift (Array.to_slice_mut a)
        let (t2, _) ← low.generic.limb64.mont.sqr_limbs t x s
        ok t2) ⦃ t1 => t1.length = 2 * m.length ∧ wordsNat t1.val = wordsNat x.val * wordsNat x.val ⦄ := by
    rw [karatsuba_sqr_eq]
    split
    · rename_i hn
      have hn' : x.length < 64 := by simpa using hn
      step as ⟨s, back, hs, _⟩
      exact hsq s (by rw [sqrNeed_small _ hn']; omega)
    · step as ⟨s, back, hs, _⟩
      exact hsq s (by
        have : s.length = 576 := by
          simp only [Slice.length]; rw [hs, Array.repeat_val, List.length_replicate]; rfl
        rw [this]; exact sqrNeed_le _ (by omega))
  step with hbranch as ⟨t1, ht1l, ht1⟩
  step with redc_spec t1 m n0 hk1 (by omega) hn0 (by rw [ht1, ht1l]; exact hT) as ⟨r, hrl, hr, hrm⟩
  rw [ht1l, show 2 * m.length - m.length = m.length by omega] at hr hrm
  rw [ht1] at hrm
  exact ⟨by omega, hr, hrm⟩

end rind.portable
