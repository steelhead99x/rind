import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Pratt certificates

A prime is proven by Lucas's test at each prime of a tree of factorizations,
checked by the kernel: the curves' fields and group orders, each up to 521
bits.
-/

namespace rind.spec

/-- `b ^ e % m`, by squaring, for `e < 2 ^ fuel`. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | fuel + 1, b, e =>
    if e = 0 then 1 % m
    else
      let r := powMod m fuel (b * b % m) (e / 2)
      if e % 2 = 0 then r else b * r % m

theorem powMod_eq (m : ℕ) : ∀ fuel b e, e < 2 ^ fuel → powMod m fuel b e = b ^ e % m
  | 0, b, e, h => by
    have : e = 0 := by simpa using h
    subst this; simp [powMod]
  | fuel + 1, b, e, h => by
    unfold powMod
    split_ifs with h0 h2
    · subst h0; simp
    · rw [powMod_eq m fuel _ _ (by rw [pow_succ] at h; omega), ← Nat.pow_mod, ← pow_two, ← pow_mul,
        Nat.two_mul_div_two_of_even (Nat.even_iff.mpr h2)]
    · rw [powMod_eq m fuel _ _ (by rw [pow_succ] at h; omega), ← Nat.pow_mod, ← pow_two, ← pow_mul,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_succ']
      congr 2
      omega

/-- Each first component is prime. -/
def PrimesAll : List (ℕ × ℕ) → Prop
  | [] => True
  | (q, _) :: fs => q.Prime ∧ PrimesAll fs

/-- Lucas's test of `p`, below 2⁵²¹, with witness `a`, for the factorization
`fs` of `p - 1` as primes and their exponents. -/
def lucasCheck (p a : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  2 ≤ p && (fs.map fun qe => qe.1 ^ qe.2).prod == p - 1 && p - 1 < 2 ^ 521 &&
    powMod p 521 a (p - 1) == 1 && fs.all fun qe => powMod p 521 a ((p - 1) / qe.1) != 1

theorem zmod_pow_eq_one {p : ℕ} (hp : 2 ≤ p) (a k : ℕ) :
    (a : ZMod p) ^ k = 1 ↔ a ^ k % p = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.one_mod_eq_one.mpr (by omega)]

theorem prime_of_lucas {p : ℕ} (a : ℕ) (fs : List (ℕ × ℕ)) (h : lucasCheck p a fs = true)
    (hfs : PrimesAll fs) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hp, hprod⟩, hlt⟩, ha⟩, hd⟩ := h
  refine lucas_primality p a ?_ ?_
  · rw [zmod_pow_eq_one hp, ← powMod_eq p 521 a _ hlt, ha]
  · intro q hq hdvd
    rw [← hprod] at hdvd
    obtain ⟨_, hm, hqd⟩ := (Prime.dvd_prod_iff hq.prime).mp hdvd
    obtain ⟨⟨q', e⟩, hqe, rfl⟩ := List.mem_map.mp hm
    have hq' : q'.Prime := by
      clear hd hqd hm hprod hdvd
      induction fs with
      | nil => cases hqe
      | cons x fs ih =>
        rcases List.mem_cons.mp hqe with rfl | hqe
        · exact hfs.1
        · exact ih hfs.2 hqe
    have : q = q' := (Nat.prime_dvd_prime_iff_eq hq hq').mp (hq.dvd_of_dvd_pow hqd)
    subst this
    intro h1
    rw [zmod_pow_eq_one hp, ← powMod_eq p 521 a _ (by have := Nat.div_le_self (p - 1) q; omega)] at h1
    exact hd _ hqe h1

end rind.spec
