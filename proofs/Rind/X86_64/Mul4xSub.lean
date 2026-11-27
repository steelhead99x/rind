import Rind.X86_64.Mul4xModel

/-! # `bn_mul4x_mont`'s final subtraction

`t - n` word by word with borrows (`diff`, `borrow`), the mask the top word
and the last borrow make, and the words it selects: `t - n` if `t ≥ n`, else
`t`, which for `t < 2n` is `t mod n` (`select_nat`). -/

open rind.x86_64.asm

namespace rind.x86_64.mul4x

/-- The borrow into word `i` of `t - n`. -/
def borrow (t n : Nat → BitVec 64) : Nat → Bool
  | 0 => false
  | i + 1 => decide ((t i).toNat < (n i).toNat + (borrow t n i).toNat)

/-- Word `i` of `t - n`. -/
def diff (t n : Nat → BitVec 64) (i : Nat) : BitVec 64 :=
  t i - n i - (BitVec.ofBool (borrow t n i)).setWidth 64

theorem diff_zero (t n : Nat → BitVec 64) : diff t n 0 = t 0 - n 0 := by
  simp only [diff, borrow]
  rw [show (BitVec.ofBool false).setWidth 64 = (0 : BitVec 64) by decide]; exact BitVec.sub_zero _

theorem diff_nat (t n : Nat → BitVec 64) (i : Nat) :
    (t i).toNat + 2 ^ 64 * (borrow t n (i + 1)).toNat =
      (diff t n i).toNat + (n i).toNat + (borrow t n i).toNat := by
  simp only [diff, borrow]
  rw [BitVec.toNat_sub, BitVec.toNat_sub, ofBool_toNat]
  have hx := (t i).isLt; have hy := (n i).isLt
  have hc : (borrow t n i).toNat ≤ 1 := Bool.toNat_le _
  by_cases h : (t i).toNat < (n i).toNat + (borrow t n i).toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

theorem val_lt (f : Nat → BitVec 64) (m : Nat) : val f m < 2 ^ (64 * m) := by
  induction m with
  | zero => simp [val, gsum]
  | succ m ih =>
    simp only [val, gsum] at ih ⊢
    have h := (f m).isLt
    have e : 2 ^ (64 * (m + 1)) = 2 ^ (64 * m) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [e]
    nlinarith

/-- `t - n` over `m` words: `t + 2^(64m)·borrow = (t - n) + n`. -/
theorem diff_chain (t n : Nat → BitVec 64) (m : Nat) :
    val t m + 2 ^ (64 * m) * (borrow t n m).toNat = val (diff t n) m + val n m := by
  induction m with
  | zero => simp [val, gsum, borrow]
  | succ m ih =>
    have h := diff_nat t n m
    have e : 2 ^ (64 * (m + 1)) = 2 ^ (64 * m) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    simp only [val, gsum] at ih ⊢
    rw [e]
    zify at ih h ⊢
    linear_combination ih + (2 : ℤ) ^ (64 * m) * h

/-- The mask `subTail` leaves: the top word less the last borrow. -/
def mask (t n : Nat → BitVec 64) (k : Nat) : BitVec 64 := t k - 0 - (BitVec.ofBool (borrow t n k)).setWidth 64

/-- The words the copy selects: `t` where the mask is set, else `t - n`. -/
def select (t n : Nat → BitVec 64) (k : Nat) (i : Nat) : BitVec 64 :=
  if mask t n k = 0 then diff t n i else t i

/-- For `t < 2n`, the mask is all ones or zero, and the selected words are `t mod n`. -/
theorem select_nat (t n : Nat → BitVec 64) (k : Nat) (hn : 0 < val n k)
    (ht : val t (k + 1) < 2 * val n k) :
    (mask t n k = 0 ∨ mask t n k = -1) ∧ val (select t n k) k < val n k ∧
      val (select t n k) k % val n k = val t (k + 1) % val n k := by
  have hN := val_lt n k
  have hT := val_lt t k
  have hD := val_lt (diff t n) k
  have hc := diff_chain t n k
  have hv : val t (k + 1) = val t k + (t k).toNat * 2 ^ (64 * k) := rfl
  have htk : (t k).toNat ≤ 1 := by
    by_contra h
    have : 2 * 2 ^ (64 * k) ≤ (t k).toNat * 2 ^ (64 * k) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hvs : val (select t n k) k = if mask t n k = 0 then val (diff t n) k else val t k := by
    unfold select
    split_ifs with h <;> rfl
  rcases Nat.lt_or_ge (t k).toNat 1 with h0 | h1
  · -- The top word is 0.
    have e0 : (t k).toNat = 0 := by omega
    have e : t k = 0 := BitVec.eq_of_toNat_eq (by simp [e0])
    rw [hv, e0, zero_mul, add_zero] at ht ⊢
    cases hb : borrow t n k
    · have hm : mask t n k = 0 := by simp [mask, e, hb]
      rw [hb] at hc; simp only [Bool.toNat_false, mul_zero, add_zero] at hc
      rw [hvs, if_pos hm]
      refine ⟨Or.inl hm, by omega, ?_⟩
      rw [show val t k = val (diff t n) k + val n k by omega, Nat.add_mod_right]
    · have hm : mask t n k = -1 := by simp [mask, e, hb]
      rw [hb] at hc; simp only [Bool.toNat_true, mul_one] at hc
      rw [hvs, if_neg (by rw [hm]; decide)]
      exact ⟨Or.inr hm, by omega, rfl⟩
  · -- The top word is 1.
    have e1 : (t k).toNat = 1 := by omega
    have e : t k = 1 := BitVec.eq_of_toNat_eq (by simp [e1])
    rw [hv, e1, one_mul] at ht ⊢
    cases hb : borrow t n k
    · rw [hb] at hc; simp only [Bool.toNat_false, mul_zero, add_zero] at hc
      omega
    · have hm : mask t n k = 0 := by simp [mask, e, hb]
      rw [hb] at hc; simp only [Bool.toNat_true, mul_one] at hc
      rw [hvs, if_pos hm]
      refine ⟨Or.inl hm, by omega, ?_⟩
      rw [show val t k + 2 ^ (64 * k) = val (diff t n) k + val n k by omega, Nat.add_mod_right]

end rind.x86_64.mul4x
