import Rind.X86_64.Asm

open rind.x86_64.asm

/-!
# `bn_mul4x_mont`'s arithmetic

The words a pass of aws-lc's `bn_mul4x_mont` computes, as the instructions
compute them (`step0`, `step`, `top0`, `top`), and what they add up to:
each pass `t' = (t + a·b[i] + q·n) / 2^64` (`pass_nat`, `pass0_nat`).
-/

namespace rind.x86_64.mul4x

/-! ## The word-serial step -/

/-- A word of a pass with no `t` to add (the first): with `c = (cA, cN)`,
`a·b + cA` and `n·q + cN` plus the former's low word; the latter's low word,
and the two high words, the next word's `c`. -/
def step0 (a n b q : BitVec 64) (c : BitVec 64 × BitVec 64) : BitVec 64 × (BitVec 64 × BitVec 64) :=
  let A := mac a b c.1
  let N := acc (mac n q c.2) A.1
  (N.1, (A.2, N.2))

/-- A word of an outer pass: `step0`, with `t` added to `a·b + cA`. -/
def step (a n t b q : BitVec 64) (c : BitVec 64 × BitVec 64) : BitVec 64 × (BitVec 64 × BitVec 64) :=
  let A := acc (mac a b c.1) t
  let N := acc (mac n q c.2) A.1
  (N.1, (A.2, N.2))

/-- The pass's top two words, from the last word's `(cA, cN)` and, in an outer pass, `t`'s top word. -/
def top0 (c : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (c.2 + c.1, (BitVec.ofBool (carry c.2 c.1)).setWidth 64)

/-- `top0` with `t`'s top word added. -/
def top (c : BitVec 64 × BitVec 64) (t : BitVec 64) : BitVec 64 × BitVec 64 := acc (top0 c) t

/-! ## What the words add up to -/

abbrev C := BitVec 64 × BitVec 64

/-- `∑ m < M, g m · 2^(64 m)`. -/
def gsum (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | M + 1 => gsum g M + g M * 2 ^ (64 * M)

/-- The number the words `f 0, …, f (n - 1)` make, least significant first. -/
abbrev val (f : Nat → BitVec 64) (n : Nat) : Nat := gsum (fun i => (f i).toNat) n

/-- A pair of carry words' sum. -/
def csum (c : C) : Nat := c.1.toNat + c.2.toNat

/-- The carries into each word of a chain of words `f m`, from `c0`. -/
def carries (f : Nat → C → BitVec 64 × C) (c0 : C) : Nat → C
  | 0 => c0
  | m + 1 => (f m (carries f c0 m)).2

/-- The low word each word of the chain leaves. -/
def stored (f : Nat → C → BitVec 64 × C) (c0 : C) (m : Nat) : BitVec 64 := (f m (carries f c0 m)).1

theorem gsum_add (g h : Nat → Nat) (M : Nat) : gsum (fun m => g m + h m) M = gsum g M + gsum h M := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [gsum, ih]; ring

theorem gsum_mul (g : Nat → Nat) (c M : Nat) : gsum (fun m => g m * c) M = gsum g M * c := by
  induction M with
  | zero => simp [gsum]
  | succ M ih => simp only [gsum, ih]; ring

theorem gsum_succ (g : Nat → Nat) (M : Nat) : gsum g (M + 1) = g 0 + 2 ^ 64 * gsum (fun m => g (m + 1)) M := by
  induction M with
  | zero => simp [gsum]
  | succ M ih =>
    rw [gsum, ih, gsum]
    have : 2 ^ (64 * (M + 1)) = 2 ^ 64 * 2 ^ (64 * M) := by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [this]; ring

theorem gsum_congr {g h : Nat → Nat} {M : Nat} (e : ∀ m < M, g m = h m) : gsum g M = gsum h M := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [gsum, ih fun m hm => e m (by omega), e M (by omega)]

theorem chain_nat (f : Nat → C → BitVec 64 × C) (g : Nat → Nat) (c0 : C)
    (hf : ∀ m c, (f m c).1.toNat + 2 ^ 64 * csum (f m c).2 = g m + csum c) (M : Nat) :
    val (stored f c0) M + 2 ^ (64 * M) * csum (carries f c0 M) = gsum g M + csum c0 := by
  induction M with
  | zero => simp [gsum, carries]
  | succ M ih =>
    have h := hf M (carries f c0 M)
    have e : 2 ^ (64 * (M + 1)) = 2 ^ (64 * M) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    simp only [val, gsum, carries, stored] at ih ⊢
    rw [e]
    zify at ih h ⊢
    linear_combination ih + (2 : ℤ) ^ (64 * M) * h

theorem step0_nat (a n b q : BitVec 64) (c : C) :
    (step0 a n b q c).1.toNat + 2 ^ 64 * csum (step0 a n b q c).2 =
      a.toNat * b.toNat + n.toNat * q.toNat + csum c := by
  have hA := mac_toNat a b c.1
  have hM := mac_toNat n q c.2
  have := mul_le n q; have := c.2.isLt; have := (mac a b c.1).1.isLt
  have hN := acc_toNat (mac n q c.2) (mac a b c.1).1 (by linarith)
  simp only [step0, csum]
  linarith

theorem step_nat (a n t b q : BitVec 64) (c : C) :
    (step a n t b q c).1.toNat + 2 ^ 64 * csum (step a n t b q c).2 =
      a.toNat * b.toNat + n.toNat * q.toNat + t.toNat + csum c := by
  have hA := mac_toNat a b c.1
  have hM := mac_toNat n q c.2
  have := mul_le n q; have := mul_le a b; have := c.1.isLt; have := c.2.isLt; have := t.isLt
  have hA' := acc_toNat (mac a b c.1) t (by linarith)
  have := (acc (mac a b c.1) t).1.isLt
  have hN := acc_toNat (mac n q c.2) (acc (mac a b c.1) t).1 (by linarith)
  simp only [step, csum]
  linarith

theorem top0_nat (c : C) : (top0 c).1.toNat + 2 ^ 64 * (top0 c).2.toNat = csum c := by
  have h1 := c.1.isLt; have h2 := c.2.isLt
  simp only [top0, csum, ofBool_toNat, carry, BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ c.2.toNat + c.1.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

theorem top0_le (c : C) : (top0 c).2.toNat ≤ 1 := by
  simp only [top0, ofBool_toNat]; exact Bool.toNat_le _

theorem top_nat (c : C) (t : BitVec 64) :
    (top c t).1.toNat + 2 ^ 64 * (top c t).2.toNat = csum c + t.toNat := by
  have h0 := top0_nat c; have h1 := top0_le c; have := (top0 c).1.isLt; have := t.isLt
  have := acc_toNat (top0 c) t (by nlinarith)
  simp only [top]
  linarith

/-! ## A pass -/

/-- The words an outer pass leaves at `t`, from `c0`, the carries into its
second word: the chain's low words, then `top`'s two. -/
def passOut (f : Nat → C → BitVec 64 × C) (c0 : C) (k : Nat) (tk : BitVec 64) (i : Nat) : BitVec 64 :=
  if i + 1 < k then stored f c0 i
  else if i + 1 = k then (top (carries f c0 (k - 1)) tk).1 else (top (carries f c0 (k - 1)) tk).2

/-- `passOut` for the first pass, whose top is `top0`'s. -/
def passOut0 (f : Nat → C → BitVec 64 × C) (c0 : C) (k : Nat) (i : Nat) : BitVec 64 :=
  if i + 1 < k then stored f c0 i
  else if i + 1 = k then (top0 (carries f c0 (k - 1))).1 else (top0 (carries f c0 (k - 1))).2

theorem val_passOut (f : Nat → C → BitVec 64 × C) (c0 : C) (K : Nat) (tk : BitVec 64) :
    val (passOut f c0 (K + 1) tk) (K + 2) = val (stored f c0) K +
      2 ^ (64 * K) * ((top (carries f c0 K) tk).1.toNat + 2 ^ 64 * (top (carries f c0 K) tk).2.toNat) := by
  simp only [val, gsum]
  rw [gsum_congr (h := fun i => (stored f c0 i).toNat) fun m hm => by simp [passOut, show m + 1 < K + 1 by omega]]
  simp only [passOut, show ¬ K + 1 < K + 1 by omega, show K + 1 = K + 1 from rfl, show ¬ K + 1 + 1 < K + 1 by omega,
    show ¬ K + 1 + 1 = K + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
  have : 2 ^ (64 * (K + 1)) = 2 ^ (64 * K) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  rw [this]; ring

theorem val_passOut0 (f : Nat → C → BitVec 64 × C) (c0 : C) (K : Nat) :
    val (passOut0 f c0 (K + 1)) (K + 2) = val (stored f c0) K +
      2 ^ (64 * K) * ((top0 (carries f c0 K)).1.toNat + 2 ^ 64 * (top0 (carries f c0 K)).2.toNat) := by
  simp only [val, gsum]
  rw [gsum_congr (h := fun i => (stored f c0 i).toNat) fun m hm => by simp [passOut0, show m + 1 < K + 1 by omega]]
  simp only [passOut0, show ¬ K + 1 < K + 1 by omega, show K + 1 = K + 1 from rfl, show ¬ K + 1 + 1 < K + 1 by omega,
    show ¬ K + 1 + 1 = K + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
  have : 2 ^ (64 * (K + 1)) = 2 ^ (64 * K) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  rw [this]; ring

/-- An outer pass: `2^64·t' = t + a·b + q·n`, if its first word's low word is 0, as `q` makes it. -/
theorem pass_nat (a n t : Nat → BitVec 64) (b q : BitVec 64) (K : Nat)
    (h0 : (mac (n 0) q (mac (a 0) b (t 0)).1).1 = 0) :
    let A0 := mac (a 0) b (t 0)
    let N0 := mac (n 0) q A0.1
    let f := fun m c => step (a (m + 1)) (n (m + 1)) (t (m + 1)) b q c
    2 ^ 64 * val (passOut f (A0.2, N0.2) (K + 1) (t (K + 1))) (K + 2) =
      val t (K + 2) + val a (K + 1) * b.toNat + q.toNat * val n (K + 1) := by
  intro A0 N0 f
  rw [val_passOut]
  have hc := chain_nat f (fun m => (a (m + 1)).toNat * b.toNat + (n (m + 1)).toNat * q.toNat + (t (m + 1)).toNat)
    (A0.2, N0.2) (fun m c => by simp only [f]; rw [step_nat]) K
  have ht := top_nat (carries f (A0.2, N0.2) K) (t (K + 1))
  have hA0 := mac_toNat (a 0) b (t 0)
  have hN0 := mac_toNat (n 0) q A0.1
  rw [h0, show (0 : BitVec 64).toNat = 0 from rfl] at hN0
  have hg : gsum (fun m => (a (m + 1)).toNat * b.toNat + (n (m + 1)).toNat * q.toNat + (t (m + 1)).toNat) K =
      gsum (fun m => (a (m + 1)).toNat) K * b.toNat + gsum (fun m => (n (m + 1)).toNat) K * q.toNat +
        gsum (fun m => (t (m + 1)).toNat) K := by
    rw [gsum_add, gsum_add, gsum_mul, gsum_mul]
  have ha := gsum_succ (fun i => (a i).toNat) K
  have hn := gsum_succ (fun i => (n i).toNat) K
  have htt : gsum (fun i => (t i).toNat) (K + 2) = (t 0).toNat + 2 ^ 64 * gsum (fun m => (t (m + 1)).toNat) K +
      2 ^ (64 * (K + 1)) * (t (K + 1)).toNat := by
    rw [gsum_succ]; simp only [gsum]; ring
  simp only [val, csum] at hc ht ha hn htt ⊢
  rw [hg] at hc
  simp only [A0, N0] at hc hA0 hN0 ⊢
  zify at hc ht hA0 hN0 ha hn htt ⊢
  rw [ha, hn, htt]
  linear_combination (2 : ℤ) ^ 64 * hc + (2 : ℤ) ^ 64 * (2 : ℤ) ^ (64 * K) * ht + hA0 + hN0

/-- The first pass: `2^64·t' = a·b + q·n`, likewise. -/
theorem pass0_nat (a n : Nat → BitVec 64) (b q : BitVec 64) (K : Nat)
    (h0 : (mac (n 0) q (mulLo (a 0) b)).1 = 0) :
    let A0 := (mulLo (a 0) b, mulHi (a 0) b)
    let N0 := mac (n 0) q A0.1
    let f := fun m c => step0 (a (m + 1)) (n (m + 1)) b q c
    2 ^ 64 * val (passOut0 f (A0.2, N0.2) (K + 1)) (K + 2) = val a (K + 1) * b.toNat + q.toNat * val n (K + 1) := by
  intro A0 N0 f
  rw [val_passOut0]
  have hc := chain_nat f (fun m => (a (m + 1)).toNat * b.toNat + (n (m + 1)).toNat * q.toNat)
    (A0.2, N0.2) (fun m c => by simp only [f]; rw [step0_nat]) K
  have ht := top0_nat (carries f (A0.2, N0.2) K)
  have hA0 := mul_toNat (a 0) b
  have hN0 := mac_toNat (n 0) q A0.1
  simp only [A0] at hN0
  rw [h0, show (0 : BitVec 64).toNat = 0 from rfl] at hN0
  have hg : gsum (fun m => (a (m + 1)).toNat * b.toNat + (n (m + 1)).toNat * q.toNat) K =
      gsum (fun m => (a (m + 1)).toNat) K * b.toNat + gsum (fun m => (n (m + 1)).toNat) K * q.toNat := by
    rw [gsum_add, gsum_mul, gsum_mul]
  have ha := gsum_succ (fun i => (a i).toNat) K
  have hn := gsum_succ (fun i => (n i).toNat) K
  simp only [val, csum] at hc ht ha hn ⊢
  rw [hg] at hc
  simp only [A0, N0] at hc hA0 hN0 ⊢
  zify at hc ht hA0 hN0 ha hn ⊢
  rw [ha, hn]
  linear_combination (2 : ℤ) ^ 64 * hc + (2 : ℤ) ^ 64 * (2 : ℤ) ^ (64 * K) * ht + hA0 + hN0

/-- `q = n0'·x` zeroes the low word of `n[0]·q + x`, for `n0' = -n[0]⁻¹ mod 2^64`. -/
theorem mulLo_eq (a b : BitVec 64) : mulLo a b = a * b := by
  apply BitVec.eq_of_toNat_eq; simp [mulLo, BitVec.toNat_mul]

theorem mac_q (n0 n0' x : BitVec 64) (h : (n0.toNat * n0'.toNat + 1) % 2 ^ 64 = 0) :
    (mac n0 (n0' * x) x).1 = 0 := by
  have e : n0 * n0' + 1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    simpa using h
  show x + mulLo n0 (n0' * x) = 0
  have e2 : x + n0 * (n0' * x) = x * (n0 * n0' + 1) := by
    have h1 : x * (1 : BitVec 64) = x := BitVec.mul_one x
    rw [BitVec.mul_add, h1, BitVec.add_comm, ← BitVec.mul_assoc, BitVec.mul_comm x]
  rw [mulLo_eq, e2, e]
  simp

end rind.x86_64.mul4x
