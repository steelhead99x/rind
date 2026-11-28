import Rind.VgChaCha20Poly1305
import Mathlib.Tactic

open rind.spec

/-!
# Poly1305 in 64-bit limbs

What aws-lc's one-pass ChaCha20-Poly1305 routines compute on x86_64 and
aarch64 alike, which the proofs of both share. Both keep the accumulator in
three 64-bit limbs, `h0 + 2^64 h1 + 2^128 h2`, below `5 · 2^128` between
blocks; add a block and the one bit above it, which keeps it below
`7 · 2^128`; multiply it exactly by `r`, which clamping keeps below
`2^124`, into four limbs; and reduce the product `t` partly, to `reduce t`,
its low 130 bits plus five times the rest, which is `t` modulo `p` and again
below `5 · 2^128` (`reduce_mod`, `reduce_lt`). They hash the AAD and the
ciphertext zero-padded to whole blocks, as RFC 8439's `macData` pads them:
`padBlocks`.
-/

namespace rind.spec.poly1305

/-- RFC 8439's accumulator from `a` over `x` zero-padded to whole 16-byte
blocks: each block, with the one bit above it, added, then times `r`,
modulo `p`. -/
def padBlocks (r a : Nat) (x : List (BitVec 8)) : Nat :=
  if h : x = [] then a else padBlocks r ((a + leNum (x.take 16) + 2 ^ 128) * r % p) (x.drop 16)
termination_by x.length
decreasing_by simp only [List.length_drop]; have := List.length_pos_of_ne_nil h; omega

@[simp] theorem padBlocks_nil (r a : Nat) : padBlocks r a [] = a := by
  rw [padBlocks]; simp

theorem padBlocks_of_ne_nil (r a : Nat) {x : List (BitVec 8)} (h : x ≠ []) :
    padBlocks r a x = padBlocks r ((a + leNum (x.take 16) + 2 ^ 128) * r % p) (x.drop 16) := by
  rw [padBlocks, dite_eq_right_iff.2 (fun h' => absurd h' h)]

/-- A block of at most 16 bytes. -/
theorem padBlocks_block (r a : Nat) {x : List (BitVec 8)} (h0 : x ≠ []) (h16 : x.length ≤ 16) :
    padBlocks r a x = (a + leNum x + 2 ^ 128) * r % p := by
  rw [padBlocks_of_ne_nil _ _ h0, List.take_of_length_le h16, List.drop_eq_nil_of_le h16, padBlocks_nil]

/-- Whole blocks, then the rest. -/
theorem padBlocks_append (r : Nat) :
    ∀ (n a : Nat) (x y : List (BitVec 8)), x.length = 16 * n →
      padBlocks r a (x ++ y) = padBlocks r (padBlocks r a x) y
  | 0, a, x, y, hx => by
    obtain rfl : x = [] := List.length_eq_zero_iff.1 (by omega)
    simp
  | n + 1, a, x, y, hx => by
    have hne : x ≠ [] := by rintro rfl; simp at hx
    rw [padBlocks_of_ne_nil _ _ (by simp [hne]), padBlocks_of_ne_nil _ _ hne,
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
    exact padBlocks_append r n _ _ _ (by simp; omega)

/-- The first `i + 1` blocks of `x`, all whole. -/
theorem padBlocks_take_succ (r a i : Nat) (x : List (BitVec 8)) (h : 16 * (i + 1) ≤ x.length) :
    padBlocks r a (x.take (16 * (i + 1))) =
      (padBlocks r a (x.take (16 * i)) + leNum ((x.drop (16 * i)).take 16) + 2 ^ 128) * r % p := by
  have e : x.take (16 * (i + 1)) = x.take (16 * i) ++ (x.drop (16 * i)).take 16 := by
    rw [show 16 * (i + 1) = 16 * i + 16 by ring, List.take_add]
  rw [e, padBlocks_append r i _ _ _ (by simp; omega),
    padBlocks_block _ _ (by simp; omega) (by simp)]

/-- `x` is its whole blocks, then a partial one, if any. -/
theorem padBlocks_whole (r a : Nat) (x : List (BitVec 8)) (h : x.length % 16 = 0) :
    padBlocks r a x = padBlocks r a (x.take (16 * (x.length / 16))) := by
  rw [List.take_of_length_le (by omega)]

theorem padBlocks_partial (r a : Nat) (x : List (BitVec 8)) (h : x.length % 16 ≠ 0) :
    padBlocks r a x = (padBlocks r a (x.take (16 * (x.length / 16))) +
      leNum (x.drop (16 * (x.length / 16))) + 2 ^ 128) * r % p := by
  conv_lhs => rw [← List.take_append_drop (16 * (x.length / 16)) x]
  rw [padBlocks_append r (x.length / 16) _ _ _ (by simp; omega),
    padBlocks_block _ _ (by simp; omega) (by simp; omega)]

/-- From below `p`, the accumulator stays below `p`. -/
theorem padBlocks_lt (r : Nat) :
    ∀ (n a : Nat) (x : List (BitVec 8)), x.length ≤ n → a < p → padBlocks r a x < p
  | 0, a, x, hx, ha => by
    obtain rfl : x = [] := List.length_eq_zero_iff.1 (by omega)
    simpa
  | n + 1, a, x, hx, ha => by
    by_cases h : x = []
    · subst h; simpa
    · rw [padBlocks_of_ne_nil _ _ h]
      exact padBlocks_lt r n _ _ (by simp; omega) (Nat.mod_lt _ (by unfold p; norm_num))

/-- The partial reduction of a product `t`: its low 130 bits plus five times
the rest. -/
def reduce (t : Nat) : Nat := t % 2 ^ 130 + 5 * (t / 2 ^ 130)

theorem reduce_mod (t : Nat) : reduce t % p = t % p := by
  simp only [reduce, p]
  omega

/-- The accumulator plus a block, times an `r` below `2^124`, as clamping
leaves it, reduces below `5 · 2^128` again. -/
theorem reduce_lt {h r : Nat} (hh : h < 7 * 2 ^ 128) (hr : r < 2 ^ 124) : reduce (h * r) < 5 * 2 ^ 128 := by
  have : h * r < 7 * 2 ^ 128 * 2 ^ 124 := Nat.mul_lt_mul'' hh hr
  unfold reduce
  have := Nat.mod_lt (h * r) (by positivity : 0 < 2 ^ 130)
  omega

/-- A step of the accumulator: from `h`, which `a` is modulo `p`, a block
`m` and the one bit above it, times `r`, reduced. -/
theorem reduce_step (h a m r : Nat) (ha : h % p = a % p) :
    reduce ((h + m + 2 ^ 128) * r) % p = (a + m + 2 ^ 128) * r % p := by
  rw [reduce_mod]
  exact ((Nat.ModEq.add_right m ha).add_right _).mul_right r

/-- Three 64-bit limbs as a number. -/
def limbs (h0 h1 h2 : BitVec 64) : Nat := h0.toNat + 2 ^ 64 * h1.toNat + 2 ^ 128 * h2.toNat

/-- `reduce` of four limbs, the low two below `2^64`: the low 130 bits are
the low two limbs and the third's low two bits, and the rest is the third's
other bits and the fourth a word up. -/
theorem reduce_limbs (t0 t1 t2 t3 : Nat) (h0 : t0 < 2 ^ 64) (h1 : t1 < 2 ^ 64) :
    reduce (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) =
      t0 + 2 ^ 64 * t1 + 2 ^ 128 * (t2 % 4) + 5 * (t2 / 4 + 2 ^ 62 * t3) := by
  unfold reduce
  omega

theorem leNum_cons (b : BitVec 8) (l : List (BitVec 8)) : leNum (b :: l) = b.toNat + 256 * leNum l := by
  simp [leNum, Nat.ofDigits_cons]

theorem leNum_append (l l' : List (BitVec 8)) : leNum (l ++ l') = leNum l + 256 ^ l.length * leNum l' := by
  simp [leNum, Nat.ofDigits_append]

theorem leNum_lt (l : List (BitVec 8)) : leNum l < 256 ^ l.length := by
  simpa [leNum] using Nat.ofDigits_lt_base_pow_length (b := 256) (l := l.map (·.toNat)) (by norm_num)
    (by simp only [List.mem_map]; rintro _ ⟨x, -, rfl⟩; exact x.isLt)

open VG.Spec.Poly1305 in
theorem bytesAt_length (m : VG.Mem) (a : VG.Addr) (n : Nat) : (bytesAt m a n).length = n := by
  simp [bytesAt]

open VG.Spec.Poly1305 in
/-- `n + k` bytes are the first `n`, then the `k` after them. -/
theorem bytesAt_add (m : VG.Mem) (a : VG.Addr) (n k : Nat) :
    bytesAt m a (n + k) = bytesAt m a n ++ bytesAt m (a + BitVec.ofNat 64 n) k := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

open VG.Spec.Poly1305 in
theorem bytesAt_take (m : VG.Mem) (a : VG.Addr) {n k : Nat} (h : k ≤ n) :
    (bytesAt m a n).take k = bytesAt m a k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

open VG.Spec.Poly1305 in
theorem bytesAt_drop (m : VG.Mem) (a : VG.Addr) {n k : Nat} (h : k ≤ n) :
    (bytesAt m a n).drop k = bytesAt m (a + BitVec.ofNat 64 k) (n - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [bytesAt_add, List.drop_left' (bytesAt_length _ _ _), Nat.add_sub_cancel_left]

open VG.Spec.Poly1305 in
theorem bytesAt_succ (m : VG.Mem) (a : VG.Addr) (n : Nat) :
    bytesAt m a (n + 1) = m a :: bytesAt m (a + 1) n := by
  rw [Nat.add_comm, bytesAt_add]
  simp [bytesAt]

/-- `n` bytes of memory as a number are the little-endian number of the bytes. -/
theorem read_toNat (m : VG.Mem) (a : VG.Addr) (n : Nat) :
    (m.read a n).toNat = leNum (VG.Spec.Poly1305.bytesAt m a n) := by
  induction n generalizing a with
  | zero => simp [VG.Mem.read, VG.Spec.Poly1305.bytesAt, leNum]
  | succ n ih =>
    rw [bytesAt_succ, VG.Mem.read, BitVec.toNat_append, ih, leNum_cons,
      ← Nat.shiftLeft_add_eq_or_of_lt (m a).isLt, Nat.shiftLeft_eq]
    ring

theorem readW64_toNat (m : VG.Mem) (a : VG.Addr) :
    (m.readW a 64).toNat = leNum (VG.Spec.Poly1305.bytesAt m a 8) := by
  rw [VG.Mem.readW, BitVec.toNat_setWidth, read_toNat]
  have := Nat.mod_lt (leNum (VG.Spec.Poly1305.bytesAt m a 8)) (by positivity : 0 < 2 ^ 64)
  rw [Nat.mod_eq_of_lt]
  rw [← read_toNat]
  exact BitVec.isLt _

end rind.spec.poly1305
