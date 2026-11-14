import Rind.P384Group

/-!
# The arithmetic of rind's P-384 comb

rind computes k·G for P-384 by the comb layout of aws-lc's
`ec_nistp_scalar_mul_base`: k's 77 Booth-recoded 5-bit windows, lowest first,
are digits `e w` in [-16, 16] whose sum of `e w · 32^w` is k, and window
`w = 4j + t` is added at tooth `t` from table `j`, which holds the multiples
of 2^(20j)·G, with five doublings between teeth.

`booth_sum` proves the windows' digits sum to k. `combAcc` is the
accumulator's multiple of G as the comb reaches each tooth and table, and
`comb_ne` proves that no addition adds equal points, which s2n-bignum's
`p384_montjmixadd` cannot: the accumulator and the table point are sums of
digits of distinct windows, which are distinct integers, and their difference
is below n except at the last window, where equality would need k ≥ n.
-/

set_option exponentiation.threshold 400

namespace rind.spec.comb384

/-! ## Booth recoding -/

/-- The digit of a 6-bit Booth window `v`, the window's 5 bits and the bit
below them: at most 16. -/
def boothD (v : Nat) : Nat := if v < 32 then (v + 1) / 2 else (64 - v) / 2

/-- The sign of a 6-bit Booth window `v`, 1 for negative. -/
def boothS (v : Nat) : Nat := if v < 32 then 0 else 1

/-- A digit and its sign as an integer. -/
def signed (d s : Nat) : Int := if s = 0 then d else -d

/-- The 6-bit Booth window `w` of `k`: bits 5w - 1 to 5w + 4, the bit below
bit 0 being zero. -/
def window (k w : Nat) : Nat := if w = 0 then 2 * k % 64 else k / 2 ^ (5 * w - 1) % 64

/-- Window `w`'s signed digit. -/
def digit (k w : Nat) : Int := signed (boothD (window k w)) (boothS (window k w))

/-- The bit below window `w`'s 5 bits. -/
def borrow (k w : Nat) : Nat := if w = 0 then 0 else k / 2 ^ (5 * w - 1) % 2

theorem window_eq (k w : Nat) : window k w = 2 * (k / 32 ^ w % 32) + borrow k w := by
  unfold window borrow
  split_ifs with hw
  · subst hw; omega
  · have h : 2 ^ (5 * w) = 2 ^ (5 * w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    rw [show (32 : Nat) ^ w = 2 ^ (5 * w) by rw [Nat.pow_mul], h, ← Nat.div_div_eq_div_mul]
    omega

theorem borrow_succ (k w : Nat) : borrow k (w + 1) = k / 32 ^ w % 32 / 16 := by
  unfold borrow
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  rw [show 5 * (w + 1) - 1 = 5 * w + 4 by omega, Nat.pow_add,
    show (32 : Nat) ^ w = 2 ^ (5 * w) by rw [Nat.pow_mul], ← Nat.div_div_eq_div_mul]
  omega

theorem borrow_le (k w : Nat) : borrow k w ≤ 1 := by
  unfold borrow; split_ifs <;> omega

theorem digit_eq (k w : Nat) :
    digit k w = (k / 32 ^ w % 32 : Nat) + borrow k w - 32 * (borrow k (w + 1) : Int) := by
  rw [digit, window_eq, borrow_succ]
  have hb := borrow_le k w
  have hc : k / 32 ^ w % 32 < 32 := Nat.mod_lt _ (by norm_num)
  generalize k / 32 ^ w % 32 = c at *
  generalize borrow k w = b at *
  interval_cases c <;> interval_cases b <;> simp [signed, boothD, boothS]

/-- The digits of the windows below `N` sum to `k mod 32^N`, less the borrow
into window `N`. -/
theorem booth_sum_mod (k N : Nat) :
    ∑ w ∈ Finset.range N, digit k w * 32 ^ w =
      (k % 32 ^ N : Nat) - (32 : Int) ^ N * borrow k N := by
  induction N with
  | zero => simp [borrow]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, digit_eq, Nat.mod_pow_succ]
    push_cast
    ring

/-- A scalar below 2^384 is the sum of its 77 windows' digits. -/
theorem booth_sum (k : Nat) (hk : k < 2 ^ 384) :
    ∑ w ∈ Finset.range 77, digit k w * 32 ^ w = k := by
  have h1 : k % 32 ^ 77 = k := Nat.mod_eq_of_lt (lt_of_lt_of_le hk (by norm_num))
  have h2 : borrow k 77 = 0 := by
    show k / 2 ^ (5 * 77 - 1) % 2 = 0
    rw [show 5 * 77 - 1 = 384 from rfl, Nat.div_eq_of_lt hk]
  rw [booth_sum_mod, h1, h2]
  simp

theorem digit_abs (k w : Nat) : |digit k w| ≤ 16 := by
  unfold digit signed boothD boothS
  have : window k w < 64 := by unfold window; split_ifs <;> omega
  split_ifs <;> simp only [abs_le] <;> constructor <;> omega

/-- The top window of a scalar below 2^384 is never negative. -/
theorem digit_76 (k : Nat) (hk : k < 2 ^ 384) : 0 ≤ digit k 76 := by
  have : window k 76 < 32 := by
    unfold window
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    have : k / 2 ^ 379 < 32 := by omega
    omega
  unfold digit signed boothS
  simp only [this, ↓reduceIte]
  exact Nat.cast_nonneg _

/-! ## Digits base 32 -/

/-- Digits base 32 below 32 in absolute value sum to zero only if each is zero. -/
theorem digits_eq_zero (N : Nat) (c : Nat → Int) (hc : ∀ i < N, |c i| < 32)
    (h : ∑ i ∈ Finset.range N, c i * 32 ^ i = 0) : ∀ i < N, c i = 0 := by
  induction N generalizing c with
  | zero => intro i hi; omega
  | succ N ih =>
    rw [Finset.sum_range_succ'] at h
    have hs : ∑ i ∈ Finset.range N, c (i + 1) * 32 ^ (i + 1) = 32 * ∑ i ∈ Finset.range N, c (i + 1) * 32 ^ i := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [hs] at h
    have h0 := abs_lt.mp (hc 0 (by omega))
    simp only [pow_zero, mul_one] at h h0
    have hc0 : c 0 = 0 := by omega
    have hrest := ih (fun i => c (i + 1)) (fun i hi => hc (i + 1) (by omega)) (by rw [hc0] at h; omega)
    intro i hi
    rcases i with _ | i
    · exact hc0
    · exact hrest i (by omega)

/-- Digits base 32 of at most 16 in absolute value sum to at most 16/31 of
32^N. -/
theorem digits_bound (N : Nat) (c : Nat → Int) (hc : ∀ i < N, |c i| ≤ 16) :
    31 * |∑ i ∈ Finset.range N, c i * 32 ^ i| ≤ 16 * (32 ^ N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i hi => hc i (by omega))
    have h2 : |c N * 32 ^ N| ≤ 16 * 32 ^ N := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : Int) < 32 ^ N)]
      exact mul_le_mul_of_nonneg_right (hc N (by omega)) (by positivity)
    have h3 := abs_add_le (∑ i ∈ Finset.range N, c i * 32 ^ i) (c N * 32 ^ N)
    rw [pow_succ]
    linarith

/-! ## The comb -/

/-- Whether window `w` has been added when the comb reaches table `j` of
tooth `t`: the windows of the teeth above `t`, and of `t` in the tables below
`j`. -/
def Added (t j w : Nat) : Bool := w < 77 && (t < w % 4 || (w % 4 == t && w / 4 < j))

theorem added_iff (t j w : Nat) : Added t j w = true ↔ w < 77 ∧ (t < w % 4 ∨ (w % 4 = t ∧ w / 4 < j)) := by
  simp [Added]

/-- The accumulator's multiple of G when the comb reaches table `j` of tooth
`t`, for windows' digits `e`: window `w` weighs 32^(w - t), which the
doublings still to come scale to 32^w. -/
def combAcc (e : Nat → Int) (t j : Nat) : Int :=
  ∑ i ∈ Finset.range 77, (if Added t j (i + t) then e (i + t) else 0) * 32 ^ i

theorem combAcc_start (e : Nat → Int) : combAcc e 3 0 = 0 := by
  unfold combAcc
  apply Finset.sum_eq_zero
  intro i _
  rw [ite_eq_right (by simp only [added_iff]; omega), zero_mul]

/-- Table `j` of tooth `t` adds window `4j + t`, weighing 2^(20j). -/
theorem combAcc_succ (e : Nat → Int) (t j : Nat) (ht : t < 4) (hj : j < 20) :
    combAcc e t (j + 1) = combAcc e t j + if 4 * j + t < 77 then e (4 * j + t) * 32 ^ (4 * j) else 0 := by
  unfold combAcc
  have hterm : ∀ i ∈ Finset.range 77,
      (if Added t (j + 1) (i + t) then e (i + t) else 0) * 32 ^ i =
        (if Added t j (i + t) then e (i + t) else 0) * 32 ^ i +
          if 4 * j = i then (if 4 * j + t < 77 then e (4 * j + t) * 32 ^ (4 * j) else 0) else 0 := by
    intro i _
    by_cases hi : 4 * j = i
    · subst hi
      have hn : Added t j (4 * j + t) = false := by
        simp only [Bool.eq_false_iff, ne_eq, added_iff]; omega
      by_cases h77 : 4 * j + t < 77
      · have hy : Added t (j + 1) (4 * j + t) = true := by simp only [added_iff]; omega
        simp [hn, hy, h77]
      · have hy : Added t (j + 1) (4 * j + t) = false := by
          simp only [Bool.eq_false_iff, ne_eq, added_iff]; omega
        simp [hn, hy, h77]
    · have he : Added t (j + 1) (i + t) = Added t j (i + t) := by
        rw [Bool.eq_iff_iff, added_iff, added_iff]; omega
      simp [hi, he]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_range, show 4 * j < 77 by omega, ↓reduceIte]

/-- Between teeth, five doublings scale the accumulator by 32. -/
theorem combAcc_tooth (e : Nat → Int) (t : Nat) (ht : t < 3) :
    combAcc e t 0 = 32 * combAcc e (t + 1) 20 := by
  unfold combAcc
  conv_lhs => rw [Finset.sum_range_succ']
  conv_rhs => rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
  have h0 : Added t 0 (0 + t) = false := by simp only [Bool.eq_false_iff, ne_eq, added_iff]; omega
  have h77 : Added (t + 1) 20 (76 + (t + 1)) = false := by simp only [Bool.eq_false_iff, ne_eq, added_iff]; omega
  simp only [h0, h77, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hA : Added t 0 (i + 1 + t) ↔ Added (t + 1) 20 (i + (t + 1)) := by
    simp only [added_iff]; omega
  rw [show i + (t + 1) = i + 1 + t by omega] at hA ⊢
  by_cases h : Added t 0 (i + 1 + t)
  · simp only [h, hA.mp h, ↓reduceIte]; ring
  · simp only [h, mt hA.mpr h]; ring

/-- After the last table of the last tooth, every window has been added at its
weight. -/
theorem combAcc_end (e : Nat → Int) :
    combAcc e 0 20 = ∑ w ∈ Finset.range 77, e w * 32 ^ w := by
  unfold combAcc
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : Added 0 20 i = true := by simp only [added_iff]; omega
  simp [this]

/-- `n384`, as an integer the comb's bounds compare with. -/
theorem n384_val : (n384 : Int) =
    39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 := by
  simp [n384]

/-- No addition of the comb adds equal points: for digits of at most 16 whose
top one is not negative and whose sum is a scalar `k` in [0, n), the
accumulator differs from the table point mod n whenever the window's digit is
not zero. -/
theorem comb_ne (e : Nat → Int) (he : ∀ w < 77, |e w| ≤ 16) (he76 : 0 ≤ e 76) (k : Nat)
    (hk : ∑ w ∈ Finset.range 77, e w * 32 ^ w = k) (hkn : k < n384) (t j : Nat) (ht : t < 4) (hj : j < 20)
    (hw : 4 * j + t < 77) (hew : e (4 * j + t) ≠ 0) :
    ¬ combAcc e t j ≡ e (4 * j + t) * 32 ^ (4 * j) [ZMOD n384] := by
  intro hmod
  set w := 4 * j + t with hwdef
  -- The difference, as digits base 32.
  set c : Nat → Int := fun i => (if Added t j (i + t) then e (i + t) else 0) - if i = 4 * j then e w else 0
    with hcdef
  have hD : combAcc e t j - e w * 32 ^ (4 * j) = ∑ i ∈ Finset.range 77, c i * 32 ^ i := by
    simp only [combAcc, hcdef, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_range, show 4 * j < 77 by omega, ↓reduceIte]
  have hnotw : ¬ Added t j w := by simp only [added_iff]; omega
  have hc16 : ∀ i < 77, |c i| ≤ 16 := by
    intro i hi
    simp only [hcdef]
    by_cases hiw : i = 4 * j
    · subst hiw
      rw [ite_eq_right hnotw, ite_eq_left rfl, zero_sub, abs_neg]
      exact he w hw
    · rw [ite_eq_right hiw, sub_zero]
      split_ifs with ha
      · exact he _ ((added_iff _ _ _).mp ha).1
      · simp
  have hcw : c (4 * j) ≠ 0 := by
    simp only [hcdef]
    rw [ite_eq_right hnotw, zero_sub, neg_ne_zero]
    exact hew
  have hne : combAcc e t j - e w * 32 ^ (4 * j) ≠ 0 := by
    rw [hD]
    intro h0
    exact hcw (digits_eq_zero 77 c (fun i hi => by have := hc16 i hi; omega) h0 (4 * j) (by omega))
  obtain ⟨m, hm⟩ : (n384 : Int) ∣ combAcc e t j - e w * 32 ^ (4 * j) := Int.ModEq.dvd hmod.symm
  have hP : (32 : Int) ^ 76 = 2 ^ 380 := by norm_num
  have hkn' : (k : Int) < n384 := by exact_mod_cast hkn
  rw [n384_val] at hm hkn'
  by_cases h76 : w = 76
  · -- The last window: t = 0 and j = 19, after every other window.
    have ht0 : t = 0 := by omega
    have hj19 : j = 19 := by omega
    subst ht0 hj19
    set A := ∑ i ∈ Finset.range 76, e i * 32 ^ i with hA
    have hacc : combAcc e 0 19 = A := by
      unfold combAcc
      rw [Finset.sum_range_succ]
      have h76' : Added 0 19 76 = false := by simp only [Bool.eq_false_iff, ne_eq, added_iff]; omega
      simp only [h76', Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have : Added 0 19 i = true := by simp only [added_iff]; omega
      simp [this]
    have hbA := digits_bound 76 e (fun i hi => he i (by omega))
    rw [← hA] at hbA
    have hA1 := le_abs_self A
    have hA2 := neg_abs_le A
    rw [Finset.sum_range_succ, ← hA] at hk
    rw [hacc] at hm
    have h16 := abs_le.mp (he 76 (by omega))
    have hw76 : w = 76 := h76
    rw [hw76] at hm hew
    rw [show 4 * 19 = 76 from rfl, hP] at hm
    rw [hP] at hk hbA
    obtain ⟨-, h16⟩ := h16
    have he1 : 1 ≤ e 76 := by omega
    have hm1 : m < 0 := by by_contra hc; linarith [not_lt.mp hc]
    have hm2 : -2 < m := by by_contra hc; linarith [not_lt.mp hc]
    obtain rfl : m = -1 := by omega
    have ha : 15 < e 76 := by by_contra hc; linarith [not_lt.mp hc]
    linarith
  · -- Every other window: the difference is below n.
    have hc76 : c 76 = 0 := by
      simp only [hcdef]
      rw [ite_eq_right (by simp only [added_iff]; omega), ite_eq_right (by omega), sub_zero]
    have hb := digits_bound 76 c (fun i hi => hc16 i (by omega))
    rw [hD, Finset.sum_range_succ, hc76, zero_mul, add_zero] at hm hne
    have hb1 := le_abs_self (∑ i ∈ Finset.range 76, c i * 32 ^ i)
    have hb2 := neg_abs_le (∑ i ∈ Finset.range 76, c i * 32 ^ i)
    rw [hP] at hb
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · omega
    · subst hm0; simp at hm; exact hne hm
    · omega

end rind.spec.comb384
