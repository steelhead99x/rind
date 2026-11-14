import Rind.N256Prime
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The arithmetic of x86_64's P-256 Booth driver

x86_64's `JacobianMontPoint::base_multiply` computes k·G as aws-lc's
`ecp_nistz256_point_mul_base` does: k's 37 Booth-recoded 7-bit windows,
lowest first, are digits `e w` in [-64, 64] whose sum of `e w · 128^w` is k,
and window `w` adds `e w · 2^(7w) · G` from table row `w`, with no doublings.

`booth_sum` proves the windows' digits sum to k. `booth_ne` proves that no
addition adds equal points, which aws-lc's `ecp_nistz256_point_add_affine`
cannot: the accumulator is the sum of the lower windows, which is smaller in
magnitude than the window's own term, and their difference is below n except
at the last window, where equality would need k ≥ n.

This follows the P-384 comb's arithmetic in kixel-ai/rind#654, base 128
instead of 32 and with no comb.
-/

set_option exponentiation.threshold 400

namespace rind.spec.booth256

/-! ## Booth recoding -/

/-- The digit of an 8-bit Booth window `v`, the window's 7 bits and the bit
below them: at most 64. -/
def boothD (v : Nat) : Nat := if v < 128 then (v + 1) / 2 else (256 - v) / 2

/-- The sign of an 8-bit Booth window `v`, 1 for negative. -/
def boothS (v : Nat) : Nat := if v < 128 then 0 else 1

/-- A digit and its sign as an integer. -/
def signed (d s : Nat) : Int := if s = 0 then d else -d

/-- The 8-bit Booth window `w` of `k`: bits 7w - 1 to 7w + 6, the bit below
bit 0 being zero. -/
def window (k w : Nat) : Nat := if w = 0 then 2 * k % 256 else k / 2 ^ (7 * w - 1) % 256

/-- Window `w`'s signed digit. -/
def digit (k w : Nat) : Int := signed (boothD (window k w)) (boothS (window k w))

/-- The bit below window `w`'s 7 bits. -/
def borrow (k w : Nat) : Nat := if w = 0 then 0 else k / 2 ^ (7 * w - 1) % 2

theorem window_lt (k w : Nat) : window k w < 256 := by
  unfold window; split <;> exact Nat.mod_lt _ (by norm_num)

theorem window_eq (k w : Nat) : window k w = 2 * (k / 128 ^ w % 128) + borrow k w := by
  unfold window borrow
  split_ifs with hw
  · subst hw; omega
  · have h : 2 ^ (7 * w) = 2 ^ (7 * w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    rw [show (128 : Nat) ^ w = 2 ^ (7 * w) by rw [Nat.pow_mul], h, ← Nat.div_div_eq_div_mul]
    omega

theorem borrow_succ (k w : Nat) : borrow k (w + 1) = k / 128 ^ w % 128 / 64 := by
  unfold borrow
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  rw [show 7 * (w + 1) - 1 = 7 * w + 6 by omega, Nat.pow_add,
    show (128 : Nat) ^ w = 2 ^ (7 * w) by rw [Nat.pow_mul], ← Nat.div_div_eq_div_mul]
  omega

theorem borrow_le (k w : Nat) : borrow k w ≤ 1 := by
  unfold borrow; split_ifs <;> omega

theorem digit_eq (k w : Nat) :
    digit k w = (k / 128 ^ w % 128 : Nat) + borrow k w - 128 * (borrow k (w + 1) : Int) := by
  rw [digit, window_eq, borrow_succ]
  have hb := borrow_le k w
  have hc : k / 128 ^ w % 128 < 128 := Nat.mod_lt _ (by norm_num)
  generalize k / 128 ^ w % 128 = c at *
  generalize borrow k w = b at *
  interval_cases c <;> interval_cases b <;> simp [signed, boothD, boothS]

/-- The digits of the windows below `N` sum to `k mod 128^N`, less the borrow
into window `N`. -/
theorem booth_sum_mod (k N : Nat) :
    ∑ w ∈ Finset.range N, digit k w * 128 ^ w =
      (k % 128 ^ N : Nat) - (128 : Int) ^ N * borrow k N := by
  induction N with
  | zero => simp [borrow]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, digit_eq, Nat.mod_pow_succ]
    push_cast
    ring

/-- A scalar below 2^256 is the sum of its 37 windows' digits. -/
theorem booth_sum (k : Nat) (hk : k < 2 ^ 256) :
    ∑ w ∈ Finset.range 37, digit k w * 128 ^ w = k := by
  have h1 : k % 128 ^ 37 = k := Nat.mod_eq_of_lt (lt_of_lt_of_le hk (by norm_num))
  have h2 : borrow k 37 = 0 := by
    show k / 2 ^ (7 * 37 - 1) % 2 = 0
    rw [show 7 * 37 - 1 = 258 from rfl, Nat.div_eq_of_lt (lt_of_lt_of_le hk (by norm_num))]
  rw [booth_sum_mod, h1, h2]
  simp

theorem boothD_le (v : Nat) (hv : v < 256) : boothD v ≤ 64 := by
  unfold boothD; split <;> omega

theorem digit_abs (k w : Nat) : |digit k w| ≤ 64 := by
  unfold digit signed boothD boothS
  have : window k w < 256 := window_lt k w
  split_ifs <;> simp only [abs_le] <;> constructor <;> omega

/-- A digit is zero exactly when its magnitude is. -/
theorem digit_eq_zero (k w : Nat) : digit k w = 0 ↔ boothD (window k w) = 0 := by
  unfold digit signed
  split <;> omega

/-- The top window of a scalar below 2^256 is in [0, 16]. -/
theorem digit_36 (k : Nat) (hk : k < 2 ^ 256) : 0 ≤ digit k 36 ∧ digit k 36 ≤ 16 := by
  have : window k 36 < 32 := by
    unfold window
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    have : k / 2 ^ 251 < 32 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      exact lt_of_lt_of_le hk (by norm_num)
    omega
  unfold digit signed boothS boothD
  simp only [show window k 36 < 128 by omega, ↓reduceIte]
  constructor
  · exact Nat.cast_nonneg _
  · have : (window k 36 + 1) / 2 ≤ 16 := by omega
    exact_mod_cast this

/-! ## No doubling -/

/-- Digits base 128 of at most 64 in absolute value sum to at most 64/127 of
128^N. -/
theorem digits_bound (N : Nat) (c : Nat → Int) (hc : ∀ i < N, |c i| ≤ 64) :
    127 * |∑ i ∈ Finset.range N, c i * 128 ^ i| ≤ 64 * (128 ^ N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i hi => hc i (by omega))
    have h2 : |c N * 128 ^ N| ≤ 64 * 128 ^ N := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : Int) < 128 ^ N)]
      exact mul_le_mul_of_nonneg_right (hc N (by omega)) (by positivity)
    have h3 := abs_add_le (∑ i ∈ Finset.range N, c i * 128 ^ i) (c N * 128 ^ N)
    rw [pow_succ]
    linarith

/-- `n256`, as an integer the bounds compare with. -/
theorem n256_val : (n256 : Int) =
    115792089210356248762697446949407573529996955224135760342422259061068512044369 := by
  simp [n256]

/-- The accumulator before window `w`: the sum of the digits below it. -/
def acc (e : Nat → Int) (w : Nat) : Int := ∑ i ∈ Finset.range w, e i * 128 ^ i

theorem acc_succ (e : Nat → Int) (w : Nat) : acc e (w + 1) = acc e w + e w * 128 ^ w := by
  simp [acc, Finset.sum_range_succ]

/-- The accumulator before the last window is below n in magnitude. -/
theorem acc_abs_lt (e : Nat → Int) (he : ∀ w < 37, |e w| ≤ 64) (w : Nat) (hw : w ≤ 36) :
    |acc e w| < n256 := by
  have hb := digits_bound w e (fun i hi => he i (by omega))
  have hp : (128 : Int) ^ w ≤ 128 ^ 36 := pow_le_pow_right₀ (by norm_num) hw
  rw [n256_val]
  unfold acc
  norm_num at hp ⊢
  linarith

/-- The accumulator is zero mod n only when it is zero. -/
theorem acc_modEq_zero (e : Nat → Int) (he : ∀ w < 37, |e w| ≤ 64) (w : Nat) (hw : w ≤ 36)
    (h : acc e w ≡ 0 [ZMOD n256]) : acc e w = 0 :=
  Int.eq_zero_of_abs_lt_dvd (Int.modEq_zero_iff_dvd.mp h) (acc_abs_lt e he w hw)

/-- No addition of the driver adds equal points: for digits of at most 64
whose top one is in [0, 16] and whose sum is a scalar `k` in [0, n), the
accumulator differs from window `w`'s term mod n whenever its digit is not
zero. -/
theorem booth_ne (e : Nat → Int) (he : ∀ w < 37, |e w| ≤ 64) (he36 : 0 ≤ e 36 ∧ e 36 ≤ 16) (k : Nat)
    (hk : acc e 37 = k) (hkn : k < n256) (w : Nat) (hw : w < 37) (hew : e w ≠ 0) :
    ¬ acc e w ≡ e w * 128 ^ w [ZMOD n256] := by
  intro hmod
  obtain ⟨m, hm⟩ : (n256 : Int) ∣ e w * 128 ^ w - acc e w := Int.ModEq.dvd hmod
  have hb : 127 * |acc e w| ≤ 64 * (128 ^ w - 1) := digits_bound w e (fun i hi => he i (by omega))
  have hA1 := le_abs_self (acc e w)
  have hA2 := neg_abs_le (acc e w)
  have hkn' : (k : Int) < n256 := by exact_mod_cast hkn
  have hk0 : (0 : Int) ≤ k := Nat.cast_nonneg _
  rw [n256_val] at hm hkn'
  have hB : (0 : Int) < 128 ^ w := by positivity
  have he1 : 1 ≤ |e w| := Int.one_le_abs hew
  have heB : |e w * 128 ^ w| = |e w| * 128 ^ w := by rw [abs_mul, abs_of_pos hB]
  have heB1 := le_abs_self (e w * 128 ^ w)
  have heB2 := neg_abs_le (e w * 128 ^ w)
  rw [heB] at heB1 heB2
  have hl : 128 ^ w ≤ |e w| * 128 ^ w := le_mul_of_one_le_left hB.le he1
  have h64 : |e w| * 128 ^ w ≤ 64 * 128 ^ w := mul_le_mul_of_nonneg_right (he w hw) hB.le
  by_cases h36 : w = 36
  · subst h36
    have hP : (128 : Int) ^ 36 = 2 ^ 252 := by norm_num
    rw [show (37 : Nat) = 36 + 1 from rfl, acc_succ] at hk
    rw [hP] at hm hb hk hl
    obtain ⟨h0, h16⟩ := he36
    have he1' : 1 ≤ e 36 := by omega
    have hm1 : 0 < m := by by_contra hc; linarith [not_lt.mp hc]
    have hm2 : m < 2 := by by_contra hc; linarith [not_lt.mp hc]
    obtain rfl : m = 1 := by omega
    have ha : 15 < e 36 := by by_contra hc; linarith [not_lt.mp hc]
    have h16' : e 36 = 16 := by omega
    rw [h16'] at hm hk
    linarith
  · have hp : (128 : Int) ^ w ≤ 128 ^ 35 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at hp
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · have : m ≤ -1 := by omega
      linarith
    · subst hm0
      simp only [mul_zero, sub_eq_zero] at hm
      rw [← hm, heB] at hb
      linarith
    · have : 1 ≤ m := by omega
      linarith

end rind.spec.booth256
