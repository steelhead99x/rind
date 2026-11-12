import Rind.SymCrypt.MlKemNtt
import Mathlib.Algebra.Field.GeomSum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# FIPS 203's NTT in closed form

FIPS 203 defines the NTT by the residues its Equations (4.12) and (4.13) name,
and computes it with Algorithms 9 and 10; SymCrypt's spec in `Rind.SymCrypt.MlKem`
transliterates those algorithms. `NTT_get` and `NTTInv_get` prove the
algorithms compute those residues and back:

* `(NTT f)[2 * i + b] = ∑ j < 128, f[2 * j + b] * ζ ^ ((2 * BitRev₇ i + 1) * j)`, and
* `(NTTInv g)[2 * j + b] = 128⁻¹ * ∑ i < 128, g[2 * i + b] * ζ⁻¹ ^ ((2 * BitRev₇ i + 1) * j)`,

with `128⁻¹ = 3303` and `ζ⁻¹ = 1175`. The forward proof follows Algorithm 9's
layers: after `l` of them, block `b` of `2 ^ l` holds the residues modulo
`X ^ (2 ^ (7 - l)) - root l b` (`Residues`). The inverse runs those layers
backwards, each merging two blocks and doubling the scale; with the roots'
orthogonality that inverts the forward closed form. s2n-bignum states its
ML-KEM postconditions with these sums, so `Rind.S2nMlKem` bridges to them.
-/

open Spec.MLKEM Symcrust.Properties.MLKEM.Ntt Finset

namespace rind.spec.mlkem

theorem get_set! (g : Polynomial) (i p : ℕ) (a : Zq) (hi : i < 256) :
    (g.set! i a)[p]! = if p = i then a else g[p]! := by
  split_ifs with h
  · exact Vector.getElem!_set! ⟨hi, h⟩
  · exact Vector.getElem!_set!_ne (Ne.symm h)

theorem nttLayerInner_get (i len start p : ℕ) (hs : start + 2 * len ≤ 256) :
    ∀ n j (g : Polynomial), len - j = n → j ≤ len →
    (nttLayerInner g i len start j)[p]! =
      if start + j ≤ p ∧ p < start + len then g[p]! + g[p + len]! * ζ ^ bitRev 7 i
      else if start + len + j ≤ p ∧ p < start + 2 * len then
        g[p - len]! - g[p]! * ζ ^ bitRev 7 i
      else g[p]! := by
  intro n
  induction n with
  | zero =>
    intro j g hn hj
    rw [nttLayerInner_unfold]
    have : ¬ j < len := by omega
    simp only [this, ite_false]
    split_ifs <;> first | omega | rfl
  | succ n ih =>
    intro j g hn hj
    rw [nttLayerInner_unfold]
    have hlt : j < len := by omega
    simp only [hlt, ite_true]
    rw [ih (j + 1) _ (by omega) (by omega)]
    simp only [get_set! _ _ _ _ (by omega : start + j + len < 256),
      get_set! _ _ _ _ (by omega : start + j < 256)]
    by_cases h1 : p = start + j
    · subst h1
      have : start + j + len ≠ start + j := by omega
      simp only [ite_true, this, ite_false]
      split_ifs <;> first | omega | ring
    · by_cases h2 : p = start + j + len
      · subst h2
        have : start + j + len - len = start + j := by omega
        simp [this]
        split_ifs <;> first | omega | ring
      · have h3 : p + len ≠ start + j + len := by omega
        simp only [h1, h2, h3, ite_false]
        split_ifs <;> first | omega | rfl

theorem nttLayer_get (len p : ℕ) (hlen : 0 < len) (hp : p < 256) :
    ∀ k c i (g : Polynomial), 2 * len * c + 2 * len * k = 256 →
    (nttLayer g i len (2 * len * c) hlen)[p]! =
      if p < 2 * len * c then g[p]!
      else if (p - 2 * len * c) % (2 * len) < len then
        g[p]! + g[p + len]! * ζ ^ bitRev 7 (i + (p - 2 * len * c) / (2 * len))
      else g[p - len]! - g[p]! * ζ ^ bitRev 7 (i + (p - 2 * len * c) / (2 * len)) := by
  intro k
  induction k with
  | zero =>
    intro c i g hk
    rw [nttLayer_unfold]
    have : ¬ 2 * len * c < 256 := by omega
    simp only [this, ite_false]
    have : p < 2 * len * c := by omega
    simp only [this, ite_true]
  | succ k ih =>
    intro c i g hk
    rw [nttLayer_unfold]
    have hc : 2 * len * c < 256 := by
      have : 0 < 2 * len * (k + 1) := by positivity
      omega
    simp only [hc, ite_true]
    have := ih (c + 1) (i + 1) (nttLayerInner g i len (2 * len * c) 0) (by rw [Nat.mul_add]; linarith)
    rw [show 2 * len * c + 2 * len = 2 * len * (c + 1) by ring, this]
    have hs : 2 * len * c + 2 * len ≤ 256 := by
      have : 0 ≤ 2 * len * k := by positivity
      nlinarith
    have inner := fun q => nttLayerInner_get i len (2 * len * c) q hs (len - 0) 0 g rfl (Nat.zero_le _)
    by_cases h1 : p < 2 * len * c
    · have : p < 2 * len * (c + 1) := by nlinarith
      simp only [h1, this, ite_true, inner]
      split_ifs <;> first | omega | rfl
    · by_cases h2 : p < 2 * len * (c + 1)
      · simp only [h1, h2, ite_true, ite_false, inner]
        have hd : (p - 2 * len * c) / (2 * len) = 0 := Nat.div_eq_of_lt (by rw [Nat.mul_add] at h2; omega)
        have hm : (p - 2 * len * c) % (2 * len) = p - 2 * len * c := Nat.mod_eq_of_lt (by rw [Nat.mul_add] at h2; omega)
        rw [hd, hm, Nat.add_zero]
        rw [Nat.mul_add] at h2
        split_ifs <;> first | omega | rfl
      · simp only [h1, h2, ite_false]
        rw [Nat.mul_add] at h2
        have e : p - 2 * len * c = (p - (2 * len * c + 2 * len)) + 2 * len := by omega
        have hd : (p - 2 * len * c) / (2 * len) = (p - (2 * len * c + 2 * len)) / (2 * len) + 1 := by
          rw [e, Nat.add_div_right _ (by omega)]
        have hm : (p - 2 * len * c) % (2 * len) = (p - (2 * len * c + 2 * len)) % (2 * len) := by
          rw [e, Nat.add_mod_right]
        have o1 : (nttLayerInner g i len (2 * len * c) 0)[p]! = g[p]! := by
          rw [inner]; split_ifs <;> first | omega | rfl
        have o2 : (nttLayerInner g i len (2 * len * c) 0)[p + len]! = g[p + len]! := by
          rw [inner]; split_ifs <;> first | omega | rfl
        rw [hd, hm, Nat.mul_add, Nat.mul_one, o1, o2, show i + 1 + (p - (2 * len * c + 2 * len)) / (2 * len)
          = i + ((p - (2 * len * c + 2 * len)) / (2 * len) + 1) by omega]
        split_ifs with h
        · rfl
        · have := Nat.mod_add_div (p - (2 * len * c + 2 * len)) (2 * len)
          have o3 : (nttLayerInner g i len (2 * len * c) 0)[p - len]! = g[p - len]! := by
            rw [inner]; split_ifs <;> first | omega | rfl
          rw [o3]

theorem nttLayer_get0 (len p : ℕ) (hlen : 0 < len) (hp : p < 256) (k : ℕ) (hk : 2 * len * k = 256)
    (i : ℕ) (g : Polynomial) :
    (nttLayer g i len 0 hlen)[p]! =
      if p % (2 * len) < len then g[p]! + g[p + len]! * ζ ^ bitRev 7 (i + p / (2 * len))
      else g[p - len]! - g[p]! * ζ ^ bitRev 7 (i + p / (2 * len)) := by
  have := nttLayer_get len p hlen hp k 0 i g (by simpa using hk)
  simpa using this

theorem sum_range_even_odd {M : Type*} [AddCommMonoid M] (F : ℕ → M) (n : ℕ) :
    ∑ s ∈ range (2 * n), F s = ∑ s ∈ range n, F (2 * s) + ∑ s ∈ range n, F (2 * s + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    abel

/-- The root of the modulus of block `b` of the `2 ^ l` blocks after `l` of
Algorithm 9's layers. -/
def root (l b : ℕ) : Zq := ζ ^ ((2 * bitRev l b + 1) * 2 ^ (7 - l))

/-- After `l` of Algorithm 9's layers, block `b` of the `2 ^ l`, each of
`2 ^ (8 - l)` coefficients, holds `κ` times `f mod (X ^ (2 ^ (8 - l)) - root l b)`. -/
def Residues (l : ℕ) (κ : Zq) (g f : Polynomial) : Prop :=
  ∀ b < 2 ^ l, ∀ t < 2 ^ (8 - l),
    g[b * 2 ^ (8 - l) + t]! = κ * ∑ s ∈ range (2 ^ l), f[t + 2 ^ (8 - l) * s]! * root l b ^ s

theorem bitRev_split : ∀ l < 7, ∀ b < 2 ^ l,
    bitRev 7 (2 ^ l + b) = (2 * bitRev (l + 1) (2 * b) + 1) * 2 ^ (7 - (l + 1)) ∧
    (2 * bitRev (l + 1) (2 * b + 1) + 1) * 2 ^ (7 - (l + 1)) = 128 + bitRev 7 (2 ^ l + b) ∧
    (2 * bitRev l b + 1) * 2 ^ (7 - l) = 2 * bitRev 7 (2 ^ l + b) := by
  decide

theorem ζ_128 : ζ ^ 128 = -1 := by decide

theorem roots (l b : ℕ) (hl : l < 7) (hb : b < 2 ^ l) :
    root (l + 1) (2 * b) = ζ ^ bitRev 7 (2 ^ l + b) ∧
    root (l + 1) (2 * b + 1) = - ζ ^ bitRev 7 (2 ^ l + b) ∧
    root l b = (ζ ^ bitRev 7 (2 ^ l + b)) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := bitRev_split l hl b hb
  refine ⟨?_, ?_, ?_⟩
  · rw [root, ← h1]
  · rw [root, h2, pow_add, ζ_128]; ring
  · rw [root, h3, mul_comm 2, pow_mul]

theorem residues_zero (f : Polynomial) : Residues 0 1 f f := by
  intro b hb t ht
  have : b = 0 := by omega
  subst this
  simp

theorem div_mod_block (len b c t : ℕ) (hc : c < 2) (ht : t < len) :
    ((2 * b + c) * len + t) / (2 * len) = b ∧ ((2 * b + c) * len + t) % (2 * len) = c * len + t := by
  have e : (2 * b + c) * len + t = (c * len + t) + b * (2 * len) := by ring
  have hlt : c * len + t < 2 * len := by
    interval_cases c <;> omega
  rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
  simp

/-- One of Algorithm 9's layers splits each block in two. -/
theorem residues_step (l : ℕ) (hl : l < 7) (g f : Polynomial) (h : Residues l 1 g f) :
    Residues (l + 1) 1 (nttLayer g (2 ^ l) (2 ^ (7 - l)) 0 (by positivity)) f := by
  intro b' hb' t ht
  set len := 2 ^ (7 - l) with hlen
  have hB' : 2 ^ (8 - (l + 1)) = len := by rw [hlen]; congr 1; omega
  have hB : 2 ^ (8 - l) = 2 * len := by
    rw [hlen, ← pow_succ']; congr 1; omega
  have hk : 2 * len * 2 ^ l = 256 := by
    rw [← hB, ← pow_add]; rw [show 8 - l + l = 8 by omega]; rfl
  rw [hB'] at ht ⊢
  obtain ⟨b, c, hc, rfl⟩ : ∃ b c, c < 2 ∧ b' = 2 * b + c := ⟨b' / 2, b' % 2, by omega, by omega⟩
  have hb : b < 2 ^ l := by rw [pow_succ] at hb'; omega
  have hp : (2 * b + c) * len + t < 256 := by
    have : (2 * b + c) * len + t < (2 * b + c + 1) * len := by nlinarith
    have : (2 * b + c + 1) * len ≤ 2 * len * 2 ^ l := by nlinarith
    omega
  obtain ⟨hd, hm⟩ := div_mod_block len b c t hc ht
  rw [nttLayer_get0 len _ (by positivity) hp (2 ^ l) hk, hd, hm]
  obtain ⟨r0, r1, r2⟩ := roots l b hl hb
  set z := ζ ^ bitRev 7 (2 ^ l + b)
  rw [pow_succ', sum_range_even_odd, one_mul]
  have hlo := h b hb t (by omega)
  have hhi := h b hb (t + len) (by omega)
  rw [hB, r2, one_mul] at hlo hhi
  interval_cases c
  · simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, show t < len from ht, ite_true]
    rw [show 2 * b * len + t = b * (2 * len) + t by ring, hlo,
      show b * (2 * len) + t + len = b * (2 * len) + (t + len) by ring, hhi, r0]
    refine congrArg₂ (· + ·) ?_ ?_
    · apply sum_congr rfl; intro s _
      rw [show t + len * (2 * s) = t + 2 * len * s by ring, pow_mul]
    · rw [Finset.sum_mul]; apply sum_congr rfl; intro s _
      rw [show t + len * (2 * s + 1) = t + len + 2 * len * s by ring, pow_succ z (2 * s), pow_mul]; ring
  · have e1 : (2 * b + 1) * len + t - len = b * (2 * len) + t := by
      have : (2 * b + 1) * len + t = b * (2 * len) + t + len := by ring
      omega
    have e2 : (2 * b + 1) * len + t = b * (2 * len) + (t + len) := by ring
    have hn : ¬ 1 * len + t < len := by omega
    rw [ite_eq_right hn, e1, hlo, e2, hhi, r1, sub_eq_add_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine congrArg₂ (· + ·) ?_ ?_
    · apply sum_congr rfl; intro s _
      rw [show t + len * (2 * s) = t + 2 * len * s by ring, pow_mul, neg_sq]
    · apply sum_congr rfl; intro s _
      rw [show t + len * (2 * s + 1) = t + len + 2 * len * s by ring, pow_succ (-z) (2 * s), pow_mul,
        neg_sq]
      ring

/-- Algorithm 9's seven layers leave the residues modulo `X ^ 2 - root 7 b`. -/
theorem ntt_residues (f : Polynomial) : Residues 7 1 (ntt f) f := by
  have r1 := residues_step 0 (by norm_num) f f (residues_zero f)
  have r2 := residues_step 1 (by norm_num) _ f r1
  have r3 := residues_step 2 (by norm_num) _ f r2
  have r4 := residues_step 3 (by norm_num) _ f r3
  have r5 := residues_step 4 (by norm_num) _ f r4
  have r6 := residues_step 5 (by norm_num) _ f r5
  have r7 := residues_step 6 (by norm_num) _ f r6
  exact r7

/-- FIPS 203's `NTT`, Algorithm 9, computes the residues (4.12) and (4.13)
define: `f mod (X ^ 2 - ζ ^ (2 * BitRev₇ i + 1))` at `2 * i` and `2 * i + 1`. -/
theorem NTT_get (f : Polynomial) (i b : ℕ) (hi : i < 128) (hb : b < 2) :
    (NTT f)[2 * i + b]! = ∑ j ∈ range 128, f[2 * j + b]! * ζ ^ ((2 * bitRev 7 i + 1) * j) := by
  rw [← ntt_eq]
  have := ntt_residues f i hi b hb
  simp only [root, show 7 - 7 = 0 from rfl, pow_zero, mul_one, one_mul] at this
  rw [show 2 * i + b = i * 2 ^ (8 - 7) + b by ring, this]
  apply sum_congr rfl; intro j _
  rw [pow_mul]; ring_nf

/-! ## Algorithm 10

Each of Algorithm 10's layers merges the residues modulo `X ^ len - z` and
`X ^ len + z` back into those modulo `X ^ (2 * len) - z ^ 2`, scaled by 2. -/

theorem invNttLayerInner_get (i len start p : ℕ) (hs : start + 2 * len ≤ 256) :
    ∀ n j (g : Polynomial), len - j = n → j ≤ len →
    (invNttLayerInner g i len start j)[p]! =
      if start + j ≤ p ∧ p < start + len then g[p]! + g[p + len]!
      else if start + len + j ≤ p ∧ p < start + 2 * len then
        ζ ^ bitRev 7 i * (g[p]! - g[p - len]!)
      else g[p]! := by
  intro n
  induction n with
  | zero =>
    intro j g hn hj
    rw [invNttLayerInner_unfold]
    have : ¬ j < len := by omega
    simp only [this, ite_false]
    split_ifs <;> first | omega | rfl
  | succ n ih =>
    intro j g hn hj
    rw [invNttLayerInner_unfold]
    have hlt : j < len := by omega
    simp only [hlt, ite_true]
    rw [ih (j + 1) _ (by omega) (by omega)]
    simp only [get_set! _ _ _ _ (by omega : start + j + len < 256),
      get_set! _ _ _ _ (by omega : start + j < 256)]
    by_cases h1 : p = start + j
    · subst h1
      have : start + j + len ≠ start + j := by omega
      simp only [ite_true, this, ite_false]
      split_ifs <;> first | omega | ring
    · by_cases h2 : p = start + j + len
      · subst h2
        have : start + j + len - len = start + j := by omega
        simp [this]
        split_ifs <;> first | omega | ring
      · have h3 : p + len ≠ start + j + len := by omega
        simp only [h1, h2, h3, ite_false]
        split_ifs <;> first | omega | rfl

theorem invNttLayer_get (len p : ℕ) (hlen : 0 < len) (hp : p < 256) :
    ∀ k c i (g : Polynomial), 2 * len * c + 2 * len * k = 256 →
    (invNttLayer g i len (2 * len * c) hlen)[p]! =
      if p < 2 * len * c then g[p]!
      else if (p - 2 * len * c) % (2 * len) < len then g[p]! + g[p + len]!
      else ζ ^ bitRev 7 (i - (p - 2 * len * c) / (2 * len)) * (g[p]! - g[p - len]!) := by
  intro k
  induction k with
  | zero =>
    intro c i g hk
    rw [invNttLayer_unfold]
    have : ¬ 2 * len * c < 256 := by omega
    simp only [this, ite_false]
    have : p < 2 * len * c := by omega
    simp only [this, ite_true]
  | succ k ih =>
    intro c i g hk
    rw [invNttLayer_unfold]
    have hc : 2 * len * c < 256 := by
      have : 0 < 2 * len * (k + 1) := by positivity
      omega
    simp only [hc, ite_true]
    have := ih (c + 1) (i - 1) (invNttLayerInner g i len (2 * len * c) 0) (by rw [Nat.mul_add]; linarith)
    rw [show 2 * len * c + 2 * len = 2 * len * (c + 1) by ring, this]
    have hs : 2 * len * c + 2 * len ≤ 256 := by
      have : 0 ≤ 2 * len * k := by positivity
      nlinarith
    have inner := fun q => invNttLayerInner_get i len (2 * len * c) q hs (len - 0) 0 g rfl (Nat.zero_le _)
    by_cases h1 : p < 2 * len * c
    · have : p < 2 * len * (c + 1) := by nlinarith
      simp only [h1, this, ite_true, inner]
      split_ifs <;> first | omega | rfl
    · by_cases h2 : p < 2 * len * (c + 1)
      · simp only [h1, h2, ite_true, ite_false, inner]
        have hd : (p - 2 * len * c) / (2 * len) = 0 := Nat.div_eq_of_lt (by rw [Nat.mul_add] at h2; omega)
        have hm : (p - 2 * len * c) % (2 * len) = p - 2 * len * c := Nat.mod_eq_of_lt (by rw [Nat.mul_add] at h2; omega)
        rw [hd, hm, Nat.sub_zero]
        rw [Nat.mul_add] at h2
        split_ifs <;> first | omega | rfl
      · simp only [h1, h2, ite_false]
        rw [Nat.mul_add] at h2
        have e : p - 2 * len * c = (p - (2 * len * c + 2 * len)) + 2 * len := by omega
        have hd : (p - 2 * len * c) / (2 * len) = (p - (2 * len * c + 2 * len)) / (2 * len) + 1 := by
          rw [e, Nat.add_div_right _ (by omega)]
        have hm : (p - 2 * len * c) % (2 * len) = (p - (2 * len * c + 2 * len)) % (2 * len) := by
          rw [e, Nat.add_mod_right]
        have o1 : (invNttLayerInner g i len (2 * len * c) 0)[p]! = g[p]! := by
          rw [inner]; split_ifs <;> first | omega | rfl
        have o2 : (invNttLayerInner g i len (2 * len * c) 0)[p + len]! = g[p + len]! := by
          rw [inner]; split_ifs <;> first | omega | rfl
        rw [hd, hm, Nat.mul_add, Nat.mul_one, o1, o2, show i - 1 - (p - (2 * len * c + 2 * len)) / (2 * len)
          = i - ((p - (2 * len * c + 2 * len)) / (2 * len) + 1) by omega]
        split_ifs with h
        · rfl
        · have := Nat.mod_add_div (p - (2 * len * c + 2 * len)) (2 * len)
          have o3 : (invNttLayerInner g i len (2 * len * c) 0)[p - len]! = g[p - len]! := by
            rw [inner]; split_ifs <;> first | omega | rfl
          rw [o3]

theorem invNttLayer_get0 (len p : ℕ) (hlen : 0 < len) (hp : p < 256) (k : ℕ) (hk : 2 * len * k = 256)
    (i : ℕ) (g : Polynomial) :
    (invNttLayer g i len 0 hlen)[p]! =
      if p % (2 * len) < len then g[p]! + g[p + len]!
      else ζ ^ bitRev 7 (i - p / (2 * len)) * (g[p]! - g[p - len]!) := by
  have := invNttLayer_get len p hlen hp k 0 i g (by simpa using hk)
  simpa using this

theorem bitRev_merge : ∀ l < 7, ∀ b < 2 ^ l,
    bitRev 7 (2 ^ (l + 1) - 1 - b) + bitRev 7 (2 ^ l + b) = 128 := by
  decide

/-- One of Algorithm 10's layers merges each pair of blocks. -/
theorem merge_step (l : ℕ) (hl : l < 7) (κ : Zq) (g f : Polynomial) (h : Residues (l + 1) κ g f) :
    Residues l (2 * κ) (invNttLayer g (2 ^ (l + 1) - 1) (2 ^ (7 - l)) 0 (by positivity)) f := by
  intro b hb t ht
  set len := 2 ^ (7 - l) with hlen
  have hB' : 2 ^ (8 - (l + 1)) = len := by rw [hlen]; congr 1; omega
  have hB : 2 ^ (8 - l) = 2 * len := by
    rw [hlen, ← pow_succ']; congr 1; omega
  have hk : 2 * len * 2 ^ l = 256 := by
    rw [← hB, ← pow_add]; rw [show 8 - l + l = 8 by omega]; rfl
  rw [hB] at ht ⊢
  have hp : b * (2 * len) + t < 256 := by
    have : b * (2 * len) + t < (b + 1) * (2 * len) := by nlinarith
    have : (b + 1) * (2 * len) ≤ 2 * len * 2 ^ l := by nlinarith
    omega
  have hd : (b * (2 * len) + t) / (2 * len) = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  have hm : (b * (2 * len) + t) % (2 * len) = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  rw [invNttLayer_get0 len _ (by positivity) hp (2 ^ l) hk, hd, hm]
  obtain ⟨r0, r1, r2⟩ := roots l b hl hb
  set z := ζ ^ bitRev 7 (2 ^ l + b)
  have hb2 : 2 * b < 2 ^ (l + 1) := by rw [pow_succ]; omega
  have hb2' : 2 * b + 1 < 2 ^ (l + 1) := by rw [pow_succ]; omega
  have hz : ζ ^ bitRev 7 (2 ^ (l + 1) - 1 - b) * z = -1 := by
    rw [← pow_add, bitRev_merge l hl b hb, ζ_128]
  set w := ζ ^ bitRev 7 (2 ^ (l + 1) - 1 - b)
  rw [r2]
  split_ifs with hlt
  · have hlo := h (2 * b) hb2 t (by rw [hB']; exact hlt)
    have hhi := h (2 * b + 1) hb2' t (by rw [hB']; exact hlt)
    rw [hB', r0] at hlo
    rw [hB', r1] at hhi
    rw [show b * (2 * len) + t = 2 * b * len + t by ring, hlo,
      show 2 * b * len + t + len = (2 * b + 1) * len + t by ring, hhi, pow_succ', sum_range_even_odd,
      sum_range_even_odd]
    simp only [mul_add, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro s _
    rw [show t + len * (2 * s) = t + 2 * len * s by ring, (even_two_mul s).neg_pow,
      (odd_two_mul_add_one s).neg_pow, ← pow_mul]
    ring
  · obtain ⟨u, rfl⟩ : ∃ u, t = len + u := ⟨t - len, by omega⟩
    have hlo := h (2 * b) hb2 u (by rw [hB']; omega)
    have hhi := h (2 * b + 1) hb2' u (by rw [hB']; omega)
    rw [hB', r0] at hlo
    rw [hB', r1] at hhi
    rw [show b * (2 * len) + (len + u) = (2 * b + 1) * len + u by ring, hhi,
      show (2 * b + 1) * len + u - len = 2 * b * len + u by
        rw [show (2 * b + 1) * len + u = 2 * b * len + u + len by ring]; omega, hlo,
      pow_succ', sum_range_even_odd, sum_range_even_odd]
    simp only [mul_add, mul_sub, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl; intro s _
    rw [show u + (len * (2 * s) + len * 1) = len + u + 2 * len * s by ring, (even_two_mul s).neg_pow,
      (odd_two_mul_add_one s).neg_pow, ← pow_mul, pow_succ]
    linear_combination (-2 * κ * f[len + u + 2 * len * s]! * z ^ (2 * s)) * hz

/-- Algorithm 10's seven layers, without its final scaling by `3303`, merge
the residues back into the coefficients scaled by 128. -/
theorem invNtt_residues (g f : Polynomial) (h : Residues 7 1 g f) :
    Residues 0 128 (invNtt g) f := by
  have r6 := merge_step 6 (by norm_num) 1 g f h
  have r5 := merge_step 5 (by norm_num) _ _ f r6
  have r4 := merge_step 4 (by norm_num) _ _ f r5
  have r3 := merge_step 3 (by norm_num) _ _ f r4
  have r2 := merge_step 2 (by norm_num) _ _ f r3
  have r1 := merge_step 1 (by norm_num) _ _ f r2
  have r0 := merge_step 0 (by norm_num) _ _ f r1
  rw [show (2 : Zq) * (2 * (2 * (2 * (2 * (2 * (2 * 1)))))) = 128 by norm_num] at r0
  exact r0

/-! ## Orthogonality of the roots

`ζ` has order 256, so the sum of `ω ^ j` over `j < 128` vanishes for each
`ω = ζ ^ (2 * m)` but 1. That makes `invClosed` a right inverse of `NTT`, and the
layer chain makes `NTTInv` a left inverse, so `NTTInv` is `invClosed`. -/

instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

theorem orderOf_ζ : orderOf ζ = 256 := by
  have h1 : ¬ ζ ^ 2 ^ 7 = 1 := by rw [show 2 ^ 7 = 128 from rfl, ζ_128]; decide
  have h2 : ζ ^ 2 ^ (7 + 1) = 1 := by
    rw [pow_succ, pow_mul, show 2 ^ 7 = 128 from rfl, ζ_128]; norm_num
  exact orderOf_eq_prime_pow h1 h2

theorem ζ_pow_eq_one (n : ℕ) : ζ ^ n = 1 ↔ 256 ∣ n := by
  rw [← orderOf_ζ, orderOf_dvd_iff_pow_eq_one]

theorem geom_ζ (m : ℕ) :
    ∑ j ∈ range 128, (ζ ^ (2 * m)) ^ j = if 128 ∣ m then 128 else 0 := by
  split_ifs with hm
  · rw [(ζ_pow_eq_one _).2 (by omega)]; simp
  · have hne : ζ ^ (2 * m) - 1 ≠ 0 := by
      rw [sub_ne_zero, Ne, ζ_pow_eq_one]; omega
    have hgeom := geom_sum_mul (ζ ^ (2 * m)) 128
    rw [← pow_mul, (ζ_pow_eq_one (2 * m * 128)).2 (by omega), sub_self] at hgeom
    exact (mul_eq_zero.1 hgeom).resolve_right hne

theorem bitRev_lt : ∀ i < 128, bitRev 7 i < 128 := by decide +kernel
theorem bitRev_bitRev : ∀ i < 128, bitRev 7 (bitRev 7 i) = i := by decide +kernel

theorem ζ_255 : ζ ^ 255 = 1175 := by decide

/-- The closed form of FIPS 203's `NTTInv`, Algorithm 10. -/
def invClosed (g : Polynomial) : Polynomial :=
  Vector.ofFn fun k =>
    3303 * ∑ i ∈ range 128, g[2 * i + k.val % 2]! * 1175 ^ ((2 * bitRev 7 i + 1) * (k.val / 2))

theorem invClosed_get (g : Polynomial) (j b : ℕ) (hj : j < 128) (hb : b < 2) :
    (invClosed g)[2 * j + b]! =
      3303 * ∑ i ∈ range 128, g[2 * i + b]! * 1175 ^ ((2 * bitRev 7 i + 1) * j) := by
  have hk : 2 * j + b < 256 := by omega
  rw [getElem!_pos (invClosed g) (2 * j + b) hk]
  simp only [invClosed, Vector.getElem_ofFn]
  rw [show (2 * j + b) % 2 = b by omega, show (2 * j + b) / 2 = j by omega]

theorem ntt_invClosed (g : Polynomial) (a b : ℕ) (ha : a < 128) (hb : b < 2) :
    (NTT (invClosed g))[2 * a + b]! = g[2 * a + b]! := by
  rw [NTT_get _ a b ha hb]
  have hF : ∀ j ∈ range 128, (invClosed g)[2 * j + b]! * ζ ^ ((2 * bitRev 7 a + 1) * j) =
      3303 * ∑ i ∈ range 128, g[2 * i + b]! *
        (ζ ^ (2 * (255 * bitRev 7 i + bitRev 7 a + 128))) ^ j := by
    intro j hj
    rw [invClosed_get g j b (mem_range.1 hj) hb, mul_assoc, sum_mul]
    refine congrArg (3303 * ·) (sum_congr rfl fun i _ => ?_)
    rw [← ζ_255, mul_assoc, ← pow_mul, ← pow_add, ← pow_mul]
    rw [show 255 * ((2 * bitRev 7 i + 1) * j) + (2 * bitRev 7 a + 1) * j =
      2 * (255 * bitRev 7 i + bitRev 7 a + 128) * j by ring]
  rw [sum_congr rfl hF, ← mul_sum, sum_comm]
  simp only [← mul_sum, geom_ζ]
  rw [sum_eq_single a]
  · have : 128 ∣ 255 * bitRev 7 a + bitRev 7 a + 128 := by omega
    rw [ite_eq_left this, ← mul_assoc, mul_comm _ (g[2 * a + b]!), mul_assoc]
    rw [show (3303 : Zq) * 128 = 1 by decide, mul_one]
  · intro i hi hia
    have h1 := bitRev_lt i (mem_range.1 hi)
    have h2 := bitRev_lt a ha
    have : bitRev 7 i ≠ bitRev 7 a := fun e => hia (by
      rw [← bitRev_bitRev i (mem_range.1 hi), e, bitRev_bitRev a ha])
    rw [ite_eq_right (by omega), mul_zero]
  · intro h; exact absurd (mem_range.2 ha) h

/-- FIPS 203's `NTTInv`, Algorithm 10, in closed form: the residues back to the coefficients. -/
theorem NTTInv_get (g : Polynomial) (j b : ℕ) (hj : j < 128) (hb : b < 2) :
    (NTTInv g)[2 * j + b]! =
      3303 * ∑ i ∈ range 128, g[2 * i + b]! * 1175 ^ ((2 * bitRev 7 i + 1) * j) := by
  have hres : Residues 7 1 g (invClosed g) := by
    intro i hi t ht
    have := ntt_residues (invClosed g) i hi t ht
    rw [← this, ntt_eq]
    simp only [show 8 - 7 = 1 from rfl, pow_one] at ht ⊢
    rw [mul_comm i 2, ntt_invClosed g i t hi ht]
  have h0 := invNtt_residues g _ hres 0 (by norm_num) (2 * j + b) (by norm_num; omega)
  simp only [pow_zero, show 8 - 0 = 8 from rfl, zero_mul, zero_add, sum_range_one, mul_zero,
    add_zero, mul_one] at h0
  rw [invNtt_eq_ntt_inv, Polynomial.getElem!_mul, h0, mul_comm, ← mul_assoc,
    show (3303 : Zq) * 128 = 1 by decide, one_mul, invClosed_get g j b hj hb]

end rind.spec.mlkem
