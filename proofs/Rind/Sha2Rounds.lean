import Aeneas
import Rind.HashSpec
import Rind.Sha2
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-256's and SHA-512's rounds and schedules, apart from any translation

FIPS 180-4's compression as a fold of `sha256Round` or `sha512Round` over
the schedule, and the schedule's recurrence, which every translation's proof
of a block function reads: `Rind.Portable.Sha256Compress` and
`Rind.Portable.Sha512Compress` for aws-lc's bodies, and `Rind.Mcu`'s for the
microcontrollers' rolled SHA-512 and ESP-IDF Xtensa's SHA-256. No module
imports two translations, so these live here.
-/

namespace rind.sha256_rounds

open rind.spec.sha256 in
/-- FIPS 180-4 section 6.2.2's round `t` of the working variables `s`, over
the schedule `W`: the step `sha256.compress` folds. -/
def sha256Round (W s : List (BitVec 32)) (t : Nat) : List (BitVec 32) :=
  let T1 := s[7]! + bigSigma1 s[4]! + ch s[4]! s[5]! s[6]! + K[t]! + W[t]!
  let T2 := bigSigma0 s[0]! + maj s[0]! s[1]! s[2]!
  [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]

theorem bv_rotate_right32 (x : U32) (k : U32) :
    (core.num.U32.rotate_right x k).bv = x.bv.rotateRight k.val := rfl

theorem ch_eq (e f g : BitVec 32) : ((f ^^^ g) &&& e) ^^^ g = ch e f g := by
  unfold ch; ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem maj_eq (a b c : BitVec 32) : ((a ^^^ b) &&& (b ^^^ c)) ^^^ b = maj a b c := by
  unfold maj; ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

/-! The message schedule. -/

/-- FIPS 180-4's schedule after `n` of its extension steps. -/
def sched (M : List (BitVec 32)) (n : Nat) : List (BitVec 32) :=
  (List.range n).foldl (fun W t => W ++ [sha256.smallSigma1 W[t + 14]! + W[t + 9]! +
    sha256.smallSigma0 W[t + 1]! + W[t]!]) M

theorem sched_succ (M : List (BitVec 32)) (n : Nat) :
    sched M (n + 1) = sched M n ++ [sha256.smallSigma1 (sched M n)[n + 14]! + (sched M n)[n + 9]! +
      sha256.smallSigma0 (sched M n)[n + 1]! + (sched M n)[n]!] := by
  simp only [sched, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sched_length (M : List (BitVec 32)) (n : Nat) : (sched M n).length = M.length + n := by
  induction n with
  | zero => simp [sched]
  | succ n ih => rw [sched_succ]; simp [ih]; omega

/-- Later steps keep the words earlier ones wrote. -/
theorem sched_get (M : List (BitVec 32)) (n m t : Nat) (ht : t < M.length + n) :
    (sched M (n + m))[t]! = (sched M n)[t]! := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, sched_succ, ← ih]
    rw [getElem!_pos _ t (by simp [sched_length]; omega),
      getElem!_pos _ t (by simp [sched_length]; omega)]
    rw [List.getElem_append_left (by simp [sched_length]; omega)]

/-- Word `t + 16` of the schedule, FIPS 180-4 section 6.2.2 step 1. -/
theorem schedule_succ (M : List (BitVec 32)) (hM : M.length = 16) (t : Nat) (ht : t < 48) :
    (sha256.schedule M)[t + 16]! = sha256.smallSigma1 (sha256.schedule M)[t + 14]! +
      (sha256.schedule M)[t + 9]! + sha256.smallSigma0 (sha256.schedule M)[t + 1]! +
      (sha256.schedule M)[t]! := by
  have hs : sha256.schedule M = sched M (t + 1 + (47 - t)) := by
    rw [show t + 1 + (47 - t) = 48 by omega]; rfl
  have hr : ∀ u, u < t + 16 → (sha256.schedule M)[u]! = (sched M t)[u]! := by
    intro u hu
    rw [hs, sched_get M (t + 1) _ u (by omega), sched_succ,
      getElem!_pos _ u (by simp [sched_length]; omega),
      getElem!_pos _ u (by simp [sched_length]; omega),
      List.getElem_append_left (by simp [sched_length]; omega)]
  rw [hr (t + 14) (by omega), hr (t + 9) (by omega), hr (t + 1) (by omega), hr t (by omega),
    hs, sched_get M (t + 1) _ _ (by omega), sched_succ,
    getElem!_pos _ (t + 16) (by simp [sched_length]; omega),
    List.getElem_append_right (by simp [sched_length]; omega)]
  simp [sched_length, hM]

/-- The schedule's first sixteen words are the block's. -/
theorem schedule_lt (M : List (BitVec 32)) (hM : M.length = 16) (t : Nat) (ht : t < 16) :
    (sha256.schedule M)[t]! = M[t]! := by
  have := sched_get M 0 48 t (by omega)
  exact this

/-- FIPS 180-4's compression of one block, as `sha256Round` folds it. -/
theorem compress_eq (H : List (BitVec 32)) (block : List Byte) :
    sha256.compress H block = List.zipWith (· + ·)
      ((List.range 64).foldl (sha256Round (sha256.schedule (rind.spec.words block))) H) H := rfl

theorem blocks_single (b : List Byte) (hb : b.length = 64) : rind.spec.blocks 64 b = [b] := by
  rw [rind.spec.blocks, ite_eq_left ⟨by omega, by omega⟩, List.take_of_length_le (by omega),
    List.drop_of_length_le (by omega)]
  unfold rind.spec.blocks; simp

theorem arr8 (st : Std.Array U32 8#usize) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7, st.val = [s0, s1, s2, s3, s4, s5, s6, s7] := by
  have h8 : st.val.length = 8 := by simp
  generalize st.val = l at h8 ⊢
  rcases l with _|⟨s0,_|⟨s1,_|⟨s2,_|⟨s3,_|⟨s4,_|⟨s5,_|⟨s6,_|⟨s7,_|⟨s8,l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | exact ⟨_, _, _, _, _, _, _, _, rfl⟩ | simp at h8

end rind.sha256_rounds

namespace rind.sha512_rounds

open rind.spec.fips512 in
/-- FIPS 180-4 section 6.4.2's round `t` of the working variables `s`, over
the schedule `W`: the step `fips512.compress` folds. -/
def sha512Round (W s : List (BitVec 64)) (t : Nat) : List (BitVec 64) :=
  let T1 := s[7]! + bigSigma1 s[4]! + ch s[4]! s[5]! s[6]! + K[t]! + W[t]!
  let T2 := bigSigma0 s[0]! + maj s[0]! s[1]! s[2]!
  [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]

theorem bv_rotate_right64 (x : U64) (k : U32) :
    (core.num.U64.rotate_right x k).bv = x.bv.rotateRight k.val := rfl

theorem ch_eq (e f g : BitVec 64) : ((f ^^^ g) &&& e) ^^^ g = fips512.ch e f g := by
  unfold fips512.ch; ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem maj_eq (a b c : BitVec 64) : ((a ^^^ b) &&& (b ^^^ c)) ^^^ b = fips512.maj a b c := by
  unfold fips512.maj; ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

/-! The message schedule. -/

/-- FIPS 180-4's schedule after `n` of its extension steps. -/
def sched (M : List (BitVec 64)) (n : Nat) : List (BitVec 64) :=
  (List.range n).foldl (fun W t => W ++ [fips512.smallSigma1 W[t + 14]! + W[t + 9]! +
    fips512.smallSigma0 W[t + 1]! + W[t]!]) M

theorem sched_succ (M : List (BitVec 64)) (n : Nat) :
    sched M (n + 1) = sched M n ++ [fips512.smallSigma1 (sched M n)[n + 14]! + (sched M n)[n + 9]! +
      fips512.smallSigma0 (sched M n)[n + 1]! + (sched M n)[n]!] := by
  simp only [sched, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sched_length (M : List (BitVec 64)) (n : Nat) : (sched M n).length = M.length + n := by
  induction n with
  | zero => simp [sched]
  | succ n ih => rw [sched_succ]; simp [ih]; omega

/-- Later steps keep the words earlier ones wrote. -/
theorem sched_get (M : List (BitVec 64)) (n m t : Nat) (ht : t < M.length + n) :
    (sched M (n + m))[t]! = (sched M n)[t]! := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, sched_succ, ← ih]
    rw [getElem!_pos _ t (by simp [sched_length]; omega),
      getElem!_pos _ t (by simp [sched_length]; omega)]
    rw [List.getElem_append_left (by simp [sched_length]; omega)]

/-- Word `t + 16` of the schedule, FIPS 180-4 section 6.4.2 step 1. -/
theorem schedule_succ (M : List (BitVec 64)) (hM : M.length = 16) (t : Nat) (ht : t < 64) :
    (fips512.schedule M)[t + 16]! = fips512.smallSigma1 (fips512.schedule M)[t + 14]! +
      (fips512.schedule M)[t + 9]! + fips512.smallSigma0 (fips512.schedule M)[t + 1]! +
      (fips512.schedule M)[t]! := by
  have hs : fips512.schedule M = sched M (t + 1 + (63 - t)) := by
    rw [show t + 1 + (63 - t) = 64 by omega]; rfl
  have hr : ∀ u, u < t + 16 → (fips512.schedule M)[u]! = (sched M t)[u]! := by
    intro u hu
    rw [hs, sched_get M (t + 1) _ u (by omega), sched_succ,
      getElem!_pos _ u (by simp [sched_length]; omega),
      getElem!_pos _ u (by simp [sched_length]; omega),
      List.getElem_append_left (by simp [sched_length]; omega)]
  rw [hr (t + 14) (by omega), hr (t + 9) (by omega), hr (t + 1) (by omega), hr t (by omega),
    hs, sched_get M (t + 1) _ _ (by omega), sched_succ,
    getElem!_pos _ (t + 16) (by simp [sched_length]; omega),
    List.getElem_append_right (by simp [sched_length]; omega)]
  simp [sched_length, hM]

/-- The schedule's first sixteen words are the block's. -/
theorem schedule_lt (M : List (BitVec 64)) (hM : M.length = 16) (t : Nat) (ht : t < 16) :
    (fips512.schedule M)[t]! = M[t]! := by
  have := sched_get M 0 64 t (by omega)
  exact this

theorem cast_setWidth {w n : Nat} (x : BitVec w) (h : w = n) : x.cast h = x.setWidth n := by
  subst h; simp

/-- Eight bytes from `k`. -/
theorem drop_take8 (l : List U8) (k : Nat) (h : k + 8 ≤ l.length) :
    (l.drop k).take 8 = [l[k]!, l[k + 1]!, l[k + 2]!, l[k + 3]!, l[k + 4]!, l[k + 5]!, l[k + 6]!,
      l[k + 7]!] := by
  apply List.ext_getElem (by simp; omega)
  intro n h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  rw [List.getElem_take, List.getElem_drop]
  rcases n with _|_|_|_|_|_|_|_|n
  all_goals first
    | omega
    | (simp only [List.getElem_cons_succ, List.getElem_cons_zero]
       rw [getElem!_pos l _ (by simp at h1; omega)]
       try rfl)

/-- FIPS 180-4's compression of one block, as `sha512Round` folds it. -/
theorem compressBlock_eq (H M : List (BitVec 64)) :
    fips512.compressBlock H M = List.zipWith (· + ·)
      ((List.range 80).foldl (sha512Round (fips512.schedule M)) H) H := rfl

theorem blockWords_length (b : List U8) : (blockWords b).length = 16 := by simp [blockWords]

theorem arr8 (st : Std.Array U64 8#usize) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7, st.val = [s0, s1, s2, s3, s4, s5, s6, s7] := by
  have h8 : st.val.length = 8 := by simp
  generalize st.val = l at h8 ⊢
  rcases l with _|⟨s0,_|⟨s1,_|⟨s2,_|⟨s3,_|⟨s4,_|⟨s5,_|⟨s6,_|⟨s7,_|⟨s8,l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | exact ⟨_, _, _, _, _, _, _, _, rfl⟩ | simp at h8

end rind.sha512_rounds
