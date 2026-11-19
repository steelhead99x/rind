import Rind.SymCrypt.MlKem
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# FIPS 203's encodings, compression, and CBD sampling in closed form

SymCrypt's spec in `Rind.SymCrypt.MlKem` transliterates FIPS 203's Algorithms
5, 6, and 8 as loops. These theorems state what the loops compute, coefficient
by coefficient and bit by bit, which is what a proof of code that packs bits
its own way needs:

* `ByteDecode_get`: coefficient `i` of `ByteDecode_d(B)` is the `d` bits of
  `B` from bit `i * d`, reduced modulo `m d`: `2^d` below 12, which leaves
  them as they are, and `q` at 12, so a field holding 3329 or more decodes to
  its residue, not its value;
* `ByteEncode_bit`: bit `k` of `ByteEncode_d(F)` is bit `k % d` of
  coefficient `k / d`;
* `SamplePolyCBD_get`: coefficient `i` of `SamplePolyCBD_η(B)` is the sum of
  the `η` bits of `B` from bit `2 * i * η`, less the sum of the next `η`;
* `Compress_val`, `Decompress_val`: the rounded quotients of Equations (4.7)
  and (4.8), as integer divisions.
-/

open Spec Spec.MLKEM

namespace rind.spec.mlkem

/-- Bit `k` of a byte string, in FIPS 203's `BytesToBits` order. -/
def bit {n : ℕ} (B : 𝔹 n) (k : ℕ) : Bool := B[k / 8]!.toNat.testBit (k % 8)

theorem getElem_bytesToBits {n : ℕ} (B : 𝔹 n) (k : ℕ) (hk : k < 8 * n) :
    (BytesToBits B)[k] = bit B k := by
  have : k / 8 < n := by omega
  simp [BytesToBits, bytesToBits, bit, this]

/-- A loop that sets each index in turn leaves `g p` at each index `p` it
reached. -/
theorem foldl_set!_get {α : Type} [Inhabited α] {N : ℕ} (g : ℕ → α) (p : ℕ) :
    ∀ (n s : ℕ) (v : Vector α N), s + n ≤ N →
      ((List.range' s n).foldl (fun F a => F.set! a (g a)) v)[p]! =
        if s ≤ p ∧ p < s + n then g p else v[p]! := by
  intro n
  induction n with
  | zero => intro s v _; simp
  | succ n ih =>
    intro s v h
    rw [List.range'_succ, List.foldl_cons, ih (s + 1) _ (by omega)]
    by_cases hp : p = s
    · subst hp
      have : ¬ (p + 1 ≤ p ∧ p < p + 1 + n) := by omega
      simp only [this, ite_false]
      rw [Vector.getElem!_set! (by omega)]
      simp
    · rw [Vector.getElem!_set!_ne (by omega)]
      by_cases h1 : s + 1 ≤ p ∧ p < s + 1 + n
      · have : s ≤ p ∧ p < s + (n + 1) := by omega
        simp only [h1, this, and_self, ite_true]
      · have : ¬ (s ≤ p ∧ p < s + (n + 1)) := by omega
        simp only [h1, this, ite_false]

/-- A spec loop whose every step is the pure update `g` is the fold of `g`. -/
theorem forIn'_fold {σ : Type} (g : ℕ → σ → σ) (l : List ℕ) (init : σ)
    (f : (a : ℕ) → a ∈ l → σ → Id (ForInStep σ))
    (hf : ∀ a h w, f a h w = pure (ForInStep.yield (g a w))) :
    forIn' l init f = pure (l.foldl (fun w a => g a w) init) := by
  have : f = fun a _ w => pure (ForInStep.yield (g a w)) := by
    funext a h w; exact hf a h w
  subst this
  simp

/-- Algorithm 5's inner loop: it writes the low `n` bits of `a` from index
`base + s`, and leaves `a` shifted down by them. -/
theorem encodeBits_fold {N : ℕ} (base : ℕ) :
    ∀ (n s : ℕ) (b : Vector Bool N) (a : ℕ), base + s + n ≤ N →
      ((List.range' s n).foldl (fun (w : Vector Bool N × ℕ) j =>
          (w.1.set! (base + j) (Bool.ofNat (w.2 % 2)), w.2 / 2)) (b, a)).2 = a / 2 ^ n ∧
      ∀ p, ((List.range' s n).foldl (fun (w : Vector Bool N × ℕ) j =>
          (w.1.set! (base + j) (Bool.ofNat (w.2 % 2)), w.2 / 2)) (b, a)).1[p]! =
        if base + s ≤ p ∧ p < base + s + n then a.testBit (p - (base + s)) else b[p]! := by
  intro n
  induction n with
  | zero => intro s b a _; simp
  | succ n ih =>
    intro s b a h
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨h2, h1⟩ := ih (s + 1) (b.set! (base + s) (Bool.ofNat (a % 2))) (a / 2) (by omega)
    refine ⟨by rw [h2, Nat.div_div_eq_div_mul, pow_succ']; , fun p => ?_⟩
    rw [h1 p]
    by_cases hp : p = base + s
    · subst hp
      have : ¬ (base + (s + 1) ≤ base + s ∧ base + s < base + (s + 1) + n) := by omega
      have h' : base + s ≤ base + s ∧ base + s < base + s + (n + 1) := by omega
      simp only [this, h', and_self, ite_true, ite_false]
      rw [Vector.getElem!_set! (by omega)]
      simp only [Nat.testBit, Bool.ofNat, Nat.sub_self, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
    · rw [Vector.getElem!_set!_ne (by omega)]
      by_cases hr : base + (s + 1) ≤ p ∧ p < base + (s + 1) + n
      · have h' : base + s ≤ p ∧ p < base + s + (n + 1) := by omega
        simp only [hr, h', and_self, ite_true]
        rw [Nat.testBit_div_two, show p - (base + (s + 1)) + 1 = p - (base + s) by omega]
      · have h' : ¬ (base + s ≤ p ∧ p < base + s + (n + 1)) := by omega
        simp only [hr, h', ite_false]

/-- Algorithm 5 drops the bit it just wrote before halving. -/
theorem sub_ofNat_div_two (x : ℕ) : (x - (Bool.ofNat (x % 2)).toNat) / 2 = x / 2 := by
  have h : (Bool.ofNat (x % 2)).toNat = x % 2 := by
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Bool.ofNat, h]
  rw [h]
  omega

/-- Algorithm 5's outer loop: after coefficients `s` to `s + n`, bit `p` of
their `d`-bit fields is bit `p % d` of coefficient `p / d`. -/
theorem encodeAll_fold {d : ℕ} (hd : 0 < d) (c : ℕ → ℕ) :
    ∀ (n s : ℕ) (b : Vector Bool (256 * d)), s + n ≤ 256 → ∀ p,
      ((List.range' s n).foldl (fun (b : Vector Bool (256 * d)) i =>
          ((List.range' 0 d).foldl (fun (w : Vector Bool (256 * d) × ℕ) j =>
            (w.1.set! (i * d + j) (Bool.ofNat (w.2 % 2)), w.2 / 2)) (b, c i)).1) b)[p]! =
        if s * d ≤ p ∧ p < (s + n) * d then (c (p / d)).testBit (p % d) else b[p]! := by
  intro n
  induction n with
  | zero => intro s b _ p; simp
  | succ n ih =>
    intro s b h p
    rw [List.range'_succ, List.foldl_cons, ih (s + 1) _ (by omega) p]
    have hin : s * d + 0 + d ≤ 256 * d := by nlinarith
    rw [(encodeBits_fold (s * d) d 0 b (c s) hin).2 p]
    have e1 : (s + 1) * d = s * d + d := by ring
    have e2 : (s + (n + 1)) * d = s * d + d + n * d := by ring
    have e3 : (s + 1 + n) * d = s * d + d + n * d := by ring
    rw [e1, e2, e3]
    by_cases h1 : s * d + d ≤ p ∧ p < s * d + d + n * d
    · have h2 : s * d ≤ p ∧ p < s * d + d + n * d := by omega
      simp only [h1, h2, and_self, ite_true]
    · by_cases h3 : s * d + 0 ≤ p ∧ p < s * d + 0 + d
      · have h2 : s * d ≤ p ∧ p < s * d + d + n * d := by
          have : 0 ≤ n * d := Nat.zero_le _
          omega
        simp only [h2, h3, and_self, ite_true]
        obtain ⟨r, rfl⟩ : ∃ r, p = r + s * d := ⟨p - s * d, by omega⟩
        have hr : r < d := by omega
        rw [Nat.add_mul_div_right _ _ hd, Nat.add_mul_mod_self_right, Nat.div_eq_of_lt hr,
          Nat.mod_eq_of_lt hr, Nat.zero_add, show r + s * d - (s * d + 0) = r by omega]
        simp only [ite_self]
      · have h2 : ¬ (s * d ≤ p ∧ p < s * d + d + n * d) := by omega
        simp only [h1, h2, h3, ite_false]

/-- Algorithm 5: bit `k` of `ByteEncode_d(F)` is bit `k % d` of coefficient
`k / d`. -/
theorem ByteEncode_bit {d : ℕ} (F : Polynomial (m d)) (h : 1 ≤ d ∧ d ≤ 12) (k : ℕ) (hk : k < 256 * d) :
    bit (ByteEncode d F h) k = (F[k / d]!).val.testBit (k % d) := by
  have hk8 : k / 8 < 32 * d := by omega
  have hbit : bit (ByteEncode d F h) k = ((ByteEncode d F h)[k / 8]'hk8).toNat.testBit (k % 8) := by
    simp [bit, hk8]
  rw [hbit]
  unfold ByteEncode
  simp only [Id.run, Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size]
  simp only [Vector.set_eq_set!, Vector.Inhabited_getElem_eq_getElem!]
  rw [forIn'_fold (fun i (b : Vector Bool (256 * d)) =>
    ((List.range' 0 d).foldl (fun (w : Vector Bool (256 * d) × ℕ) j =>
      (w.1.set! (i * d + j) (Bool.ofNat (w.2 % 2)), w.2 / 2)) (b, (F[i]!).val)).1)]
  · simp only [pure_bind]
    change (BitVec.toNat (BitsToBytes _)[k / 8]!).testBit (k % 8) = _
    rw [show ∀ (v : 𝔹 (32 * d)), v[k / 8]! = v[k / 8]'hk8 from fun v => getElem!_pos v _ hk8,
      bitsToBytes_testBit _ _ hk8 _ (Nat.mod_lt _ (by norm_num)), Vector.getElem_cast]
    simp only [Vector.Inhabited_getElem_eq_getElem!, Nat.div_add_mod]
    rw [show (256 - 0 + 1 - 1) / 1 = 256 by norm_num,
      encodeAll_fold (by omega) (fun i => (F[i]!).val) 256 0 _ (by norm_num) k]
    simp [hk]
  · intro a ha w
    have ha' : a < 256 := by simpa using ha
    rw [forIn'_fold (fun j (w : Vector Bool (256 * d) × ℕ) =>
      (w.1.set! (a * d + j) (Bool.ofNat (w.2 % 2)), w.2 / 2))]
    · simp
    · intro j hj b
      have hj' : j < d := by simpa using hj
      have hlt : a * d + j < 256 * d := by nlinarith
      rw [Vector.getElem!_set! (by simpa using hlt)]
      rw [sub_ofNat_div_two]

/-- A spec loop whose every step sets index `a` to `g a` is the fold that
does. -/
theorem forIn'_set! {α : Type} [Inhabited α] {N : ℕ} (g : ℕ → α) (l : List ℕ) (v : Vector α N)
    (f : (a : ℕ) → a ∈ l → Vector α N → Id (ForInStep (Vector α N)))
    (hf : ∀ a h w, f a h w = pure (ForInStep.yield (w.set! a (g a)))) :
    forIn' l v f = pure (l.foldl (fun F a => F.set! a (g a)) v) := by
  have : f = fun a _ w => pure (ForInStep.yield (w.set! a (g a))) := by
    funext a h w; exact hf a h w
  subst this
  simp

/-- Algorithm 6: coefficient `i` of `ByteDecode_d(B)` is the sum of the `d`
bits of `B` from bit `i * d`, each times its power of two, as an element of
`ZMod (m d)`: unchanged below `d = 12`, and reduced modulo `q` at 12, where a
field can hold up to 4095. -/
theorem ByteDecode_get {d : ℕ} (B : 𝔹 (32 * d)) (h : 1 ≤ d ∧ d ≤ 12) (i : ℕ) (hi : i < 256) :
    (ByteDecode B h)[i]! = ((∑ j : Fin d, (bit B (i * d + j)).toNat * 2 ^ j.val : ℕ) : ZMod (m d)) := by
  unfold ByteDecode
  simp only [Id.run, Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size]
  simp only [Vector.set_eq_set!]
  rw [forIn'_set! (fun a => ((∑ j : Fin d, (bit B (a * d + j)).toNat * 2 ^ j.val : ℕ) : ZMod (m d)))]
  · simp only [bind_pure]
    show (List.foldl _ _ _)[i]! = _
    rw [foldl_set!_get _ _ _ _ _ (by norm_num)]
    simp [hi]
  · intro a ha w
    have ha' : a < 256 := by simpa using ha
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [getElem_bytesToBits]

/-- Algorithm 8: coefficient `i` of `SamplePolyCBD_η(B)` is the sum of the
`η` bits of `B` from bit `2 * i * η`, less the sum of the `η` after them. -/
theorem SamplePolyCBD_get {η : Η} (B : 𝔹 (64 * η)) (i : ℕ) (hi : i < 256) :
    (SamplePolyCBD B)[i]! =
      ((∑ j : Fin η, (bit B (2 * i * η + j)).toNat : ℕ) : Zq) -
        ((∑ j : Fin η, (bit B (2 * i * η + η + j)).toNat : ℕ) : Zq) := by
  unfold SamplePolyCBD
  simp only [Id.run, Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size]
  simp only [Vector.set_eq_set!]
  rw [forIn'_set! (fun a => ((∑ j : Fin η, (bit B (2 * a * η + j)).toNat : ℕ) : Zq) -
    ((∑ j : Fin η, (bit B (2 * a * η + η + j)).toNat : ℕ) : Zq))]
  · simp only [bind_pure]
    show (List.foldl _ _ _)[i]! = _
    rw [foldl_set!_get _ _ _ _ _ (by norm_num)]
    simp [hi]
  · intro a ha w
    have ha' : a < 256 := by simpa using ha
    simp only [getElem_bytesToBits]

theorem rat_round_div (x y : ℕ) (hy : y ≠ 0) :
    Aeneas.rat_round ((x : ℚ) / (y : ℚ)) = ((2 * x + y) / (2 * y) : ℕ) := by
  simp only [Aeneas.rat_round]
  have : (x : ℚ) / y + 1 / 2 = ((2 * x + y : ℕ) : ℚ) / ((2 * y : ℕ) : ℚ) := by
    have : (y : ℚ) ≠ 0 := by exact_mod_cast hy
    push_cast
    field_simp
  rw [this, Rat.floor_natCast_div_natCast]
  norm_cast

/-- Equation (4.8): `Decompress_d(y)` is `⌊(q * y + 2^(d-1)) / 2^d⌋`. -/
theorem Decompress_val (d : ℕ) (y : ZMod (m d)) (h : 1 ≤ d ∧ d < 12) :
    Decompress d y h = (((q * y.val + 2 ^ (d - 1)) / 2 ^ d : ℕ) : Zq) := by
  unfold Decompress
  have e : ((q : ℚ) / (2 ^ d : ℚ)) * (y.val : ℚ) = ((q * y.val : ℕ) : ℚ) / ((2 ^ d : ℕ) : ℚ) := by
    push_cast; ring
  rw [e, rat_round_div _ _ (by positivity)]
  have : (2 * (q * y.val) + 2 ^ d) / (2 * 2 ^ d) = (q * y.val + 2 ^ (d - 1)) / 2 ^ d := by
    obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, show 2 * (q * y.val) + 2 ^ c * 2 = 2 * (q * y.val + 2 ^ c) by ring,
      show 2 * (2 ^ c * 2) = 2 * (2 ^ c * 2) from rfl, Nat.mul_div_mul_left _ _ (by norm_num)]
  rw [this, Int.cast_natCast]

/-- Equation (4.7): `Compress_d(x)` is `⌊(2^(d+1) * x + q) / 2q⌋ mod 2^d`. -/
theorem Compress_val (d : ℕ) (x : Zq) (h : 1 ≤ d ∧ d < 12) :
    Compress d x h = (((2 * (2 ^ d * x.val) + q) / (2 * q) : ℕ) : ZMod (m d)) := by
  unfold Compress
  have e : ((2 ^ d : ℚ) / (q : ℚ)) * (x.val : ℚ) = ((2 ^ d * x.val : ℕ) : ℚ) / ((q : ℕ) : ℚ) := by
    push_cast; ring
  rw [e, rat_round_div _ _ (by decide), Int.cast_natCast]

/-- Byte strings with the same bits are the same. -/
theorem eq_of_bit {n : ℕ} (B B' : 𝔹 n) (h : ∀ k < 8 * n, bit B k = bit B' k) : B = B' := by
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · have := h (8 * i + t) (by omega)
    simp only [bit] at this
    rw [show (8 * i + t) / 8 = i by omega, show (8 * i + t) % 8 = t by omega, getElem!_pos B i hi,
      getElem!_pos B' i hi] at this
    exact this
  · have hlt : ∀ b : Byte, b.toNat < 2 ^ t := fun b =>
      lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow (hlt _), Nat.testBit_lt_two_pow (hlt _)]

end rind.spec.mlkem
