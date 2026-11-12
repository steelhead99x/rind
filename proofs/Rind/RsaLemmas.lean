import Rind.Rsa
import Rind.Spec
import Mathlib.Tactic
open Aeneas Aeneas.Std

/-! Arithmetic the RSA proofs rest on: Montgomery reduction's bound, and the
quotient estimate of one step of Knuth's algorithm D, each over `Nat`. -/

namespace rind.spec.rsa

/-! ## Montgomery reduction -/

/-- A Montgomery reduction's result is below twice the modulus: `n·q + a`
is `R·T` for `q < R` and `a < n²`, with `n < R`. -/
theorem redc_lt {n q a T R : Nat} (hR : n < R) (hq : q < R) (ha : a < n * n)
    (heq : n * q + a = R * T) : T < 2 * n := by
  by_contra h
  push Not at h
  have h1 : R * (2 * n) ≤ R * T := Nat.mul_le_mul_left _ h
  have h2 : n * q < n * R := Nat.mul_lt_mul_of_pos_left hq (by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at ha
    · exact hn)
  have h3 : n * n ≤ n * R := Nat.mul_le_mul_left _ hR.le
  nlinarith

/-- A Montgomery reduction's result is `a / R` modulo `n`. -/
theorem redc_mod {n q a T R : Nat} (heq : n * q + a = R * T) : T * R % n = a % n := by
  rw [Nat.mul_comm, ← heq, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]

/-! ## One step of Knuth's algorithm D

`N = T3·S + rN` is divided by `D = D2·S + rD`, each `rN` and `rD` below `S`:
`T3` is the dividend's top three words and `D2` the divisor's top two. -/

section knuth
variable {S T3 D2 rN rD : Nat}

/-- A quotient digit whose product with `D2` exceeds `T3` is too large. -/
theorem knuth_gt (hrN : rN < S) (q : Nat) (hq : T3 < q * D2) :
    (T3 * S + rN) / (D2 * S + rD) < q := by
  have hS : 0 < S := by omega
  rw [Nat.div_lt_iff_lt_mul (by
    rcases Nat.eq_zero_or_pos D2 with h | h
    · subst h; simp at hq
    · positivity)]
  have : (T3 + 1) * S ≤ q * D2 * S := Nat.mul_le_mul_right _ hq
  nlinarith

/-- A quotient digit at most `T3 / D2` is at most one too large, for
`D2` of at least `B` and `T3` below `(D2 + 1)·B`. -/
theorem knuth_le_succ (hrD : rD < S) {B : Nat} (hB0 : 0 < B) (hB : B ≤ D2) (hT : T3 < (D2 + 1) * B)
    (q : Nat) (hq : q * D2 ≤ T3) : q ≤ (T3 * S + rN) / (D2 * S + rD) + 1 := by
  have hS : 0 < S := by omega
  have hD2 : 0 < D2 + 1 := by omega
  -- `T3 / (D2 + 1)` is at most the quotient, since `D < (D2 + 1)·S`.
  have hlow : T3 / (D2 + 1) ≤ (T3 * S + rN) / (D2 * S + rD) := by
    rw [Nat.le_div_iff_mul_le (by nlinarith)]
    have h1 : T3 / (D2 + 1) * (D2 + 1) ≤ T3 := Nat.div_mul_le_self _ _
    have h2 : T3 / (D2 + 1) * rD ≤ T3 / (D2 + 1) * S := Nat.mul_le_mul_left _ hrD.le
    nlinarith
  -- and `q` at most `T3 / D2`, which is at most one more.
  have hq' : q ≤ T3 / D2 := (Nat.le_div_iff_mul_le (by omega)).mpr hq
  have hstep : T3 / D2 ≤ T3 / (D2 + 1) + 1 := by
    set s := T3 / (D2 + 1)
    set r := T3 % (D2 + 1)
    have hdecomp : T3 = (D2 + 1) * s + r := (Nat.div_add_mod _ _).symm
    have hr : r < D2 + 1 := Nat.mod_lt _ hD2
    have hs : s < B := by
      rw [Nat.div_lt_iff_lt_mul hD2]
      nlinarith
    rw [Nat.div_le_iff_le_mul_add_pred (by omega), hdecomp, Nat.mul_succ, Nat.succ_mul]
    omega
  omega

end knuth

/-- The first estimate, the top two words of `U` over `D`'s top word, or
`B - 1` when those reach it, is at least `U / D`: `U` is `T2·S + rU` and `D`
at least `d1·S`, with `U < D·B`. -/
theorem knuth_q0_ge {B S T2 rU D d1 : Nat} (hrU : rU < S) (hD : d1 * S ≤ D) (hUD : T2 * S + rU < D * B)
    (hd1 : 0 < d1) : (T2 * S + rU) / D ≤ if T2 / B < d1 then T2 / d1 else B - 1 := by
  have hS : 0 < S := by omega
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; simp at hUD
    · exact h
  have hQB : (T2 * S + rU) / D < B := by
    rw [Nat.div_lt_iff_lt_mul hDpos]; linarith
  split
  · rw [Nat.le_div_iff_mul_le hd1]
    set Q := (T2 * S + rU) / D
    have h1 : Q * D ≤ T2 * S + rU := Nat.div_mul_le_self _ _
    have h2 : Q * (d1 * S) ≤ Q * D := Nat.mul_le_mul_left _ hD
    have h3 : Q * d1 * S < (T2 + 1) * S := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right h3
    omega
  · omega

/-- A quotient digit `q` with `Q ≤ q ≤ Q + 1` for `Q = U / D`, whose
product with `D` is subtracted from `U` as `low`, the `K`-word difference,
and the words `u2 - cy - bw` above it. The difference is `U mod D` when the
words above do not go negative, and `low + D - K` is when they do. -/
theorem msub_result {U D K q low u2 cy bw : Nat} (hD : 0 < D) (hDK : D ≤ K) (hlow : low < K)
    (hbw : bw ≤ 1) (hq1 : U / D ≤ q) (hq2 : q ≤ U / D + 1)
    (heq : (U : Int) - q * D = low + K * ((u2 : Int) - cy - bw)) :
    (¬(u2 < cy ∨ (u2 = cy ∧ bw = 1)) → low = U % D) ∧
      ((u2 < cy ∨ (u2 = cy ∧ bw = 1)) → K ≤ low + D ∧ low + D - K = U % D) := by
  have hdm := Nat.div_add_mod U D
  have hr := Nat.mod_lt U hD
  set Q := U / D
  set r := U % D
  have hU : (U : Int) = Q * D + r := by rw [Nat.mul_comm] at hdm; exact_mod_cast hdm.symm
  rcases (show q = Q ∨ q = Q + 1 by omega) with rfl | rfl
  · -- `U - q·D` is `r`, below `D`, so no borrow reaches above.
    have h : (r : Int) = low + K * ((u2 : Int) - cy - bw) := by rw [← heq, hU]; ring
    have ht : (u2 : Int) - cy - bw = 0 := by
      rcases lt_trichotomy ((u2 : Int) - cy - bw) 0 with h1 | h1 | h1
      · nlinarith
      · exact h1
      · nlinarith
    refine ⟨fun _ => by rw [ht] at h; omega, fun hneg => ?_⟩
    exfalso; omega
  · -- `U - q·D` is `r - D`, negative.
    have h : (r : Int) - D = low + K * ((u2 : Int) - cy - bw) := by rw [← heq, hU]; push_cast; ring
    have ht : (u2 : Int) - cy - bw = -1 := by
      rcases lt_trichotomy ((u2 : Int) - cy - bw) (-1) with h1 | h1 | h1
      · nlinarith
      · exact h1
      · have : 0 ≤ (u2 : Int) - cy - bw := by omega
        nlinarith
    refine ⟨fun hpos => ?_, fun _ => ?_⟩
    · exfalso; omega
    · rw [ht] at h; omega


/-! ## Limbs -/

theorem wordsNat_lt' (w : List U64) : rind.spec.wordsNat w < 2 ^ (64 * w.length) := by
  unfold rind.spec.wordsNat
  have := Nat.ofDigits_lt_base_pow_length (b := 2 ^ 64) (l := w.map (·.val)) (by norm_num)
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact y.hBounds)
  simpa [pow_mul] using this

theorem wordsNat_append (a b : List U64) :
    rind.spec.wordsNat (a ++ b) = rind.spec.wordsNat a + 2 ^ (64 * a.length) * rind.spec.wordsNat b := by
  simp only [rind.spec.wordsNat, List.map_append, Nat.ofDigits_append, List.length_map, pow_mul]

theorem wordsNat_cons (x : U64) (l : List U64) :
    rind.spec.wordsNat (x :: l) = x.val + 2 ^ 64 * rind.spec.wordsNat l := by
  simp [rind.spec.wordsNat, Nat.ofDigits_cons]

theorem wordsNat_nil : rind.spec.wordsNat [] = 0 := rfl

theorem wordsNat_replicate_zero (n : Nat) : rind.spec.wordsNat (List.replicate n 0#u64) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, wordsNat_cons, ih]; simp

theorem wordsNat_take_drop (l : List U64) (i : Nat) :
    rind.spec.wordsNat l = rind.spec.wordsNat (l.take i) +
      2 ^ (64 * (l.take i).length) * rind.spec.wordsNat (l.drop i) := by
  rw [← wordsNat_append, List.take_append_drop]

theorem wordsNat_take_mod (l : List U64) (k : Nat) :
    rind.spec.wordsNat (l.take k) = rind.spec.wordsNat l % 2 ^ (64 * k) := by
  have h := wordsNat_take_drop l k
  by_cases hk : k ≤ l.length
  · have hlen : (l.take k).length = k := by simp [hk]
    rw [hlen] at h
    have hlt := wordsNat_lt' (l.take k)
    rw [hlen] at hlt
    rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · have ht : l.take k = l := List.take_of_length_le (by omega)
    have hlt := wordsNat_lt' l
    rw [ht, Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-! ## Montgomery exponentiation -/

/-- A Montgomery product's result, by `R` coprime to `n`, cancelled. -/
theorem mont_cancel {n R a b : Nat} (hR : Nat.Coprime R n) (h : a * R ≡ b * R [MOD n]) :
    a ≡ b [MOD n] :=
  Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hR) h

theorem coprime_two_pow_odd {n : Nat} (hn : n % 2 = 1) (k : Nat) : Nat.Coprime (2 ^ k) n :=
  Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr hn))

/-- One bit of `e`, down from its top: `e / 2^j` is twice `e / 2^(j+1)`, plus the bit. -/
theorem div_two_pow_succ (e j : Nat) : e / 2 ^ j = 2 * (e / 2 ^ (j + 1)) + e / 2 ^ j % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

section mont_exp
variable {N R A C : Nat} (hR : Nat.Coprime R N)
include hR

/-- Squaring `C^t` in the Montgomery domain gives `C^(2t)`. -/
theorem mont_exp_sqr {S t : Nat} (hA : A ≡ C ^ t * R [MOD N]) (hS : S * R ≡ A * A [MOD N]) :
    S ≡ C ^ (2 * t) * R [MOD N] := by
  apply mont_cancel hR
  refine hS.trans ((hA.mul hA).trans (by unfold Nat.ModEq; congr 1; ring))

/-- Multiplying `C^t` by `C` in the Montgomery domain gives `C^(t+1)`. -/
theorem mont_exp_mul {M Cm t : Nat} (hA : A ≡ C ^ t * R [MOD N]) (hCm : Cm ≡ C * R [MOD N])
    (hM : M * R ≡ A * Cm [MOD N]) : M ≡ C ^ (t + 1) * R [MOD N] := by
  apply mont_cancel hR
  refine hM.trans ((hA.mul hCm).trans (by unfold Nat.ModEq; congr 1; ring))

/-- Multiplying `C^t` by `C` itself leaves the Montgomery domain with `C^(t+1)`. -/
theorem mont_exp_out {M t : Nat} (hA : A ≡ C ^ t * R [MOD N]) (hM : M * R ≡ A * C [MOD N]) :
    M ≡ C ^ (t + 1) [MOD N] := by
  apply mont_cancel hR
  refine hM.trans ((hA.mul_right C).trans (by unfold Nat.ModEq; congr 1; ring))

end mont_exp

end rind.spec.rsa
