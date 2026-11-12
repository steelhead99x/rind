import Rind.X86_64.Ghash
open Aeneas Aeneas.Std Result rind.vale rind.simd Polynomial

/-!
# rind's PCLMULQDQ GHASH

`Rind.X86_64.AesGcmModel`'s `ClmulTable::add`, `_mul8`, and `mul_h` hash
blocks as Vale's `ghash_LE` does, for a table of the key's powers: each sums
the Karatsuba products of several blocks with descending powers and reduces
once, which `Rind.Gf128`'s `reduce_sum` and `mul_data` prove is Horner's rule
on the blocks, the state being the polynomial of the hash's bytes reversed.
-/

local notation "P" => Polynomial (ZMod 2)

-- Unfolding the recursions below over polynomials, whose zero and sum are
-- deep terms, needs more than the project's depth.
set_option maxRecDepth 20000

namespace rind.x86_64

/-! ## GHASH on polynomials -/

/-- GHASH from the state `c` over the blocks `bs`, each a polynomial of a
block's bytes reversed, under the key `H`. -/
noncomputable def ghashPoly (H c : P) (bs : List P) : P :=
  bs.foldl (fun a b => gf128MulRev (a + b) H) c

/-- The blocks `xs` times descending powers of `H`, the last times `H`. -/
noncomputable def sumPow (H : P) : List P → P
  | [] => 0
  | x :: xs => gf128MulRev x (gPower H (xs.length + 1)) + sumPow H xs

theorem ghashPoly_cons (H c b : P) (bs : List P) :
    ghashPoly H c (b :: bs) = ghashPoly H (gf128MulRev (c + b) H) bs := by
  rw [ghashPoly, ghashPoly, List.foldl_cons]

theorem ghashPoly_nil (H c : P) : ghashPoly H c [] = c := by rw [ghashPoly, List.foldl_nil]

theorem sumPow_nil (H : P) : sumPow H [] = 0 := by rw [sumPow]

theorem sumPow_cons (H x : P) (xs : List P) :
    sumPow H (x :: xs) = gf128MulRev x (gPower H (xs.length + 1)) + sumPow H xs := by
  rw [sumPow]

theorem gPower_one (H : P) : gPower H 1 = H := rfl

theorem mulRev_add_right (a b c : P) : gf128MulRev a (b + c) = gf128MulRev a b + gf128MulRev a c := by
  rw [mulRev_comm, mulRev_add_left, mulRev_comm, mulRev_comm c]

theorem mulRev_zero_left (a : P) : gf128MulRev 0 a = 0 := by
  have := mulRev_add_left 0 0 a
  rw [add_zero] at this
  have h2 : (2 : P) = 0 := two_eq_zero_P
  linear_combination this + gf128MulRev 0 a * h2

theorem mulRev_pow (H a : P) (n : ℕ) (hn : 1 ≤ n) :
    gf128MulRev (gf128MulRev a H) (gPower H n) = gf128MulRev a (gPower H (n + 1)) := by
  rw [mulRev_assoc, gPower_succ H hn]

/-- Horner's rule: GHASH over at least one block is the state times `H` to
their number, plus the blocks times descending powers. -/
theorem ghashPoly_eq (H : P) : ∀ (bs : List P) (c : P), bs ≠ [] →
    ghashPoly H c bs = gf128MulRev c (gPower H bs.length) + sumPow H bs
  | [], _, h => absurd rfl h
  | [b], c, _ => by
    rw [ghashPoly_cons, ghashPoly_nil, sumPow_cons, sumPow_nil, List.length_cons,
      List.length_nil, gPower_one, add_zero, mulRev_add_left]
  | b :: b' :: bs, c, _ => by
    have ih := ghashPoly_eq H (b' :: bs) (gf128MulRev (c + b) H) (by simp)
    rw [ghashPoly_cons, ih, mulRev_pow _ _ _ (by simp), mulRev_add_left, sumPow_cons (xs := b' :: bs)]
    simp only [List.length_cons]
    ring

/-! ## The PCLMULQDQ steps -/

/-- A table for the GHASH key `H`: H to H^8, each shifted as Vale's
`shift_key_1` does, and beside each its halves XORed. -/
def TableFor (H : P) (t : low.x86_64.ghash.ClmulTable) : Prop :=
  ∀ i < 8, toPoly t.powers.val[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower H (i + 1)) ∧
    t.powers_xor.val[i]! = swap t.powers.val[i]! ^^^ t.powers.val[i]!

theorem mul_model_eq (lo mi hi x h : BitVec 128) :
    low.x86_64.ghash.mul lo mi hi x h (swap h ^^^ h) =
      ok ((karaTerms x h).1 ^^^ lo, (karaTerms x h).2.1 ^^^ mi, (karaTerms x h).2.2 ^^^ hi) := by
  have e0 : (I32.bv 0#i32).getLsbD 0 = false := by decide
  have e4 : (I32.bv 0#i32).getLsbD 4 = false := by decide
  have f0 : (I32.bv 17#i32).getLsbD 0 = true := by decide
  have f4 : (I32.bv 17#i32).getLsbD 4 = true := by decide
  simp only [low.x86_64.ghash.mul, core.core_arch.x86.sse2._mm_shuffle_epi32,
    core.core_arch.x86.sse2._mm_xor_si128, core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128,
    swap_lanes, bind_ok, e0, e4, f0, f4, Bool.false_eq_true, ite_false, ite_true, lane64_0, lane64_1,
    karaTerms]

theorem reduce_model_eq (lo mi hi : BitVec 128) :
    low.x86_64.ghash.reduce lo mi hi = ok (reduceModel lo mi hi) := by
  have e0 : (I32.bv 0#i32).getLsbD 0 = false := by decide
  have e4 : (I32.bv 0#i32).getLsbD 4 = false := by decide
  simp only [low.x86_64.ghash.reduce, low.x86_64.ghash.GF128_POLY_HI,
    core.core_arch.x86.sse2._mm_shuffle_epi32, core.core_arch.x86.sse2._mm_xor_si128,
    core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128, swap_lanes, bind_ok, e0, e4,
    Bool.false_eq_true, ite_false, lane64_0, poly_hi_lo, reduceModel]

/-- `kara` of the terms after a `mul!`. -/
theorem kara_mul (lo mi hi x h : BitVec 128) :
    kara ((karaTerms x h).1 ^^^ lo) ((karaTerms x h).2.1 ^^^ mi) ((karaTerms x h).2.2 ^^^ hi) =
      toPoly x * toPoly h + kara lo mi hi := by
  rw [kara_xor, kara_karaTerms]

theorem kara_zero : kara 0 0 0 = 0 := by simp [kara, toPoly_zero']


/-! ## Loads -/

theorem byte_reverseBytes (v : Quad32) {i : Nat} (hi : i < 16) :
    byte (reverseBytesQuad32 v) i = byte v (15 - i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byte _ _ hj, getLsbD_byte _ _ hj, getLsbD_reverseBytesQuad32 _ (by omega)]
  congr 1; omega

/-- `PSHUFB` by `BYTESWAP` reverses the bytes. -/
theorem shuffle_byteswap (v : BitVec 128) :
    core.core_arch.x86.ssse3._mm_shuffle_epi8 v 0x00010203_04050607_08090a0b_0c0d0e0f#128 =
      ok (reverseBytesQuad32 v) := by
  simp only [core.core_arch.x86.ssse3._mm_shuffle_epi8]
  congr 1

/-- A block of bytes as GHASH's multiplies take it: its bytes reversed. -/
def blockBE (b : List U8) : BitVec 128 := reverseBytesQuad32 (low.x86_64.aes.load b)

theorem load_be_eq (b : List U8) : low.x86_64.ghash.load_be b = ok (blockBE b) := by
  simp only [low.x86_64.ghash.load_be, low.x86_64.ghash.BYTESWAP, bind_ok, shuffle_byteswap, blockBE]

/-! ## Karatsuba terms summed -/

/-- `mul!` over pairs of data and power, from the terms `acc`. -/
def accum (acc : BitVec 128 × BitVec 128 × BitVec 128) :
    List (BitVec 128 × BitVec 128) → BitVec 128 × BitVec 128 × BitVec 128
  | [] => acc
  | (x, h) :: ps => accum ((karaTerms x h).1 ^^^ acc.1, (karaTerms x h).2.1 ^^^ acc.2.1,
      (karaTerms x h).2.2 ^^^ acc.2.2) ps

theorem accum_append (acc : BitVec 128 × BitVec 128 × BitVec 128) (l1 l2 : List (BitVec 128 × BitVec 128)) :
    accum acc (l1 ++ l2) = accum (accum acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => rfl
  | cons p l1 ih => obtain ⟨x, h⟩ := p; exact ih _

theorem kara_accum (acc : BitVec 128 × BitVec 128 × BitVec 128) (ps : List (BitVec 128 × BitVec 128)) :
    kara (accum acc ps).1 (accum acc ps).2.1 (accum acc ps).2.2 =
      kara acc.1 acc.2.1 acc.2.2 + (ps.map fun p => toPoly p.1 * toPoly p.2).sum := by
  induction ps generalizing acc with
  | nil => simp [accum]
  | cons p ps ih =>
    obtain ⟨x, h⟩ := p
    rw [accum, ih, kara_mul, List.map_cons, List.sum_cons]
    ring

/-- The terms of the pairs `ps`, reduced once. -/
def reduceAll (ps : List (BitVec 128 × BitVec 128)) : BitVec 128 :=
  let a := accum (0, 0, 0) ps
  reduceModel a.1 a.2.1 a.2.2

theorem toPoly_reduceAll (ps : List (BitVec 128 × BitVec 128)) :
    toPoly (reduceAll ps) = (ps.map fun p => toPoly (mulModel p.1 p.2)).sum :=
  reduce_sum _ _ _ ps (by rw [kara_accum]; simp only [kara_zero, zero_add])

/-- The powers H^n down to H, as the table holds them. -/
def powersDesc (t : low.x86_64.ghash.ClmulTable) (n : Nat) : List (BitVec 128) :=
  (List.range n).reverse.map fun i => t.powers.val[i]!

theorem powersDesc_succ (t : low.x86_64.ghash.ClmulTable) (n : Nat) :
    powersDesc t (n + 1) = t.powers.val[n]! :: powersDesc t n := by
  simp [powersDesc, List.range_succ]

/-- Data times the table's powers, H^n for the first of `n` down to H for
the last, summed, is `sumPow`. -/
theorem sum_powersDesc (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) :
    ∀ xs : List (BitVec 128), xs.length ≤ 8 →
      ((xs.zip (powersDesc t xs.length)).map fun p => toPoly (mulModel p.1 p.2)).sum =
        sumPow H (xs.map toPoly)
  | [], _ => by simp [powersDesc, sumPow_nil]
  | x :: xs, hl => by
    rw [List.length_cons, powersDesc_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      sum_powersDesc H hH t ht xs (by simp at hl; omega), List.map_cons, sumPow_cons, List.length_map,
      mul_data _ _ _ (small_gPower H hH _) ((ht xs.length (by simp at hl; omega)).1)]

theorem toPoly_reduceAll_powers (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable)
    (ht : TableFor H t) (xs : List (BitVec 128)) (hl : xs.length ≤ 8) :
    toPoly (reduceAll (xs.zip (powersDesc t xs.length))) = sumPow H (xs.map toPoly) := by
  rw [toPoly_reduceAll, sum_powersDesc H hH t ht xs hl]

/-! ## `_mul8` and `mul_h` -/

theorem powersDesc_eight (t : low.x86_64.ghash.ClmulTable) :
    powersDesc t 8 = [t.powers.val[7]!, t.powers.val[6]!, t.powers.val[5]!, t.powers.val[4]!,
      t.powers.val[3]!, t.powers.val[2]!, t.powers.val[1]!, t.powers.val[0]!] := rfl

theorem mul8_eq (H : P) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (x1 x2 x3 x4 x5 x6 x7 x8 : BitVec 128) :
    low.x86_64.ghash._mul8 t x1 x2 x3 x4 x5 x6 x7 x8 =
      ok (reduceAll ([x1, x2, x3, x4, x5, x6, x7, x8].zip (powersDesc t 8))) := by
  simp only [low.x86_64.ghash._mul8, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok,
    (ht 0 (by omega)).2, (ht 1 (by omega)).2, (ht 2 (by omega)).2, (ht 3 (by omega)).2,
    (ht 4 (by omega)).2, (ht 5 (by omega)).2, (ht 6 (by omega)).2, (ht 7 (by omega)).2,
    mul_model_eq, reduce_model_eq, powersDesc_eight, reduceAll, accum, List.zip_cons_cons,
    List.zip_nil_left]
  rfl

theorem mul_h_eq (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (x : BitVec 128) :
    ∃ y, low.x86_64.ghash.ClmulTable.mul_h t x = ok y ∧ toPoly y = gf128MulRev (toPoly x) H := by
  refine ⟨reduceAll ([x].zip (powersDesc t 1)), ?_, ?_⟩
  · simp only [low.x86_64.ghash.ClmulTable.mul_h, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok,
      (ht 0 (by omega)).2, mul_model_eq, reduce_model_eq, reduceAll, accum, powersDesc,
      List.range_one, List.reverse_singleton, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_left]
    rfl
  · have h1 := toPoly_reduceAll_powers H hH t ht [x] (by simp)
    rw [List.length_singleton] at h1
    rw [h1, List.map_cons, List.map_nil, sumPow_cons,
      sumPow_nil, List.length_nil, gPower_one, add_zero]

/-! ## Chunks -/

theorem chunksOf_length {α : Type} (k : Nat) (l : List α) : (chunksOf k l).length = l.length / k := by
  simp [chunksOf]

theorem chunksOf_of_lt {α : Type} {k : Nat} {l : List α} (h : l.length < k) : chunksOf k l = [] := by
  simp [chunksOf, Nat.div_eq_of_lt h]

theorem chunksOf_cons {α : Type} {k : Nat} {l : List α} (hk : 0 < k) (h : k ≤ l.length) :
    chunksOf k l = l.take k :: chunksOf k (l.drop k) := by
  unfold chunksOf
  rw [List.length_drop, Nat.div_eq_sub_div hk h, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.mul_zero, List.drop_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, List.drop_drop]
  congr 2
  rw [Nat.mul_succ]; omega

theorem chunksRest_cons {α : Type} {k : Nat} {l : List α} (hk : 0 < k) (h : k ≤ l.length) :
    chunksRest k l = chunksRest k (l.drop k) := by
  unfold chunksRest
  rw [List.length_drop, Nat.div_eq_sub_div hk h, List.drop_drop]
  congr 1
  rw [Nat.mul_succ]; omega

theorem chunksRest_of_lt {α : Type} {k : Nat} {l : List α} (h : l.length < k) : chunksRest k l = l := by
  simp [chunksRest, Nat.div_eq_of_lt h]

theorem chunksRest_length {α : Type} (k : Nat) (l : List α) : (chunksRest k l).length = l.length % k := by
  simp only [chunksRest, List.length_drop]
  have := Nat.div_add_mod l.length k
  omega

theorem chunksOf_length_mem {α : Type} {k : Nat} {l c : List α} (h : c ∈ chunksOf k l) :
    c.length = k := by
  simp only [chunksOf, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  have h1 : k * (i + 1) ≤ l.length :=
    le_trans (Nat.mul_le_mul_left k (by omega : i + 1 ≤ l.length / k)) (Nat.mul_div_le l.length k)
  rw [Nat.mul_succ] at h1
  simp only [List.length_take, List.length_drop]
  omega

/-! ## `add_tail` -/

/-- The blocks `bs` with the state `x` XORed into the first. -/
def tailInputs (x : BitVec 128) : List (BitVec 128) → List (BitVec 128)
  | [] => []
  | b :: bs => (x ^^^ b) :: bs

theorem tailInputs_cons (x b : BitVec 128) (bs : List (BitVec 128)) :
    tailInputs x (b :: bs) = (x ^^^ b) :: bs := rfl

theorem tailInputs_zero (bs : List (BitVec 128)) : tailInputs 0 bs = bs := by
  cases bs <;> simp [tailInputs]

theorem tailInputs_append (x : BitVec 128) (a b : List (BitVec 128)) (ha : a ≠ []) :
    tailInputs x (a ++ b) = tailInputs x a ++ b := by
  cases a with
  | nil => exact absurd rfl ha
  | cons a t => rfl

theorem length_tailInputs (x : BitVec 128) (bs : List (BitVec 128)) :
    (tailInputs x bs).length = bs.length := by
  cases bs <;> simp [tailInputs]

/-- GHASH from `x` over `bs` is the blocks with `x` XORed into the first,
times descending powers. -/
theorem sumPow_tailInputs (H : P) (x : BitVec 128) (bs : List (BitVec 128)) (hb : bs ≠ []) :
    sumPow H ((tailInputs x bs).map toPoly) = ghashPoly H (toPoly x) (bs.map toPoly) := by
  cases bs with
  | nil => exact absurd rfl hb
  | cons b bs =>
    rw [ghashPoly_eq H _ _ (by simp), tailInputs, List.map_cons, List.map_cons, sumPow_cons, sumPow_cons,
      toPoly_xor, mulRev_add_left]
    simp only [List.length_map, List.length_cons]
    ring

theorem add_tail_loop_eq (x lo mi hi : BitVec 128) :
    ∀ (blocks : List (List U8)) (ps : List (BitVec 128 × BitVec 128)),
      blocks.length ≤ ps.length → (∀ p ∈ ps, p.2 = swap p.1 ^^^ p.1) →
      low.x86_64.ghash.ClmulTable.add_tail_loop blocks ps x lo mi hi =
        let a := accum (lo, mi, hi) ((tailInputs x (blocks.map blockBE)).zip (ps.map Prod.fst))
        ok (if blocks = [] then x else 0, a.1, a.2.1, a.2.2, ps.drop blocks.length)
  | [], ps, _, _ => by simp [low.x86_64.ghash.ClmulTable.add_tail_loop, tailInputs, accum]
  | _ :: _, [], hl, _ => by simp at hl
  | b :: bs, (h, hx) :: ps, hl, hp => by
    have hhx : hx = swap h ^^^ h := hp (h, hx) (by simp)
    subst hhx
    rw [low.x86_64.ghash.ClmulTable.add_tail_loop]
    simp only [load_be_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok, mul_model_eq,
      core.core_arch.x86.sse2._mm_setzero_si128]
    simp only [add_tail_loop_eq 0 _ _ _ bs ps (by simp at hl; omega) (fun p hp' => hp p (by simp [hp']))]
    simp only [tailInputs_zero]
    simp only [List.map_cons, tailInputs_cons, List.zip_cons_cons, accum, List.length_cons,
      List.drop_succ_cons, List.cons_ne_nil, ite_false, ite_self]
    rfl

/-- The table's first `n` powers, each beside its halves XORed, from H^n down. -/
theorem zip_take_reverse (t : low.x86_64.ghash.ClmulTable) (n : Nat) (hn : n ≤ 8) :
    ((t.powers.val.take n).zip (t.powers_xor.val.take n)).reverse =
      (List.range n).reverse.map fun i => (t.powers.val[i]!, t.powers_xor.val[i]!) := by
  rw [List.map_reverse]
  congr 1
  have h1 : t.powers.val.length = 8 := by simp
  have h2 : t.powers_xor.val.length = 8 := by simp
  apply List.ext_getElem
  · simp only [List.length_zip, List.length_take, List.length_map, List.length_range]
    omega
  · intro i hi _
    simp only [List.length_zip, List.length_take] at hi
    have i1 : i < t.powers.val.length := by omega
    have i2 : i < t.powers_xor.val.length := by omega
    simp [List.getElem_zip, List.getElem_take, List.getElem?_eq_getElem i1, List.getElem?_eq_getElem i2]

/-- The bytes `rest`, fewer than a block, zero-padded and reversed. -/
def tailBlock (rest : List U8) : BitVec 128 := blockBE (rest ++ List.replicate (16 - rest.length) 0#u8)

/-- The blocks GHASH takes from `bytes`: the whole ones, then the rest padded. -/
def padBlocks (bytes : List U8) : List (BitVec 128) :=
  (chunksOf 16 bytes).map blockBE ++
    if chunksRest 16 bytes = [] then [] else [tailBlock (chunksRest 16 bytes)]

theorem length_padBlocks (bytes : List U8) : (padBlocks bytes).length = (bytes.length + 15) / 16 := by
  have h := chunksRest_length 16 bytes
  rw [padBlocks, List.length_append, List.length_map, chunksOf_length]
  split
  · rename_i he; rw [he] at h; simp at h; simp; omega
  · rename_i he
    have : (chunksRest 16 bytes).length ≠ 0 := by simpa using he
    simp; omega

theorem range_succ_reverse {α : Type} (f : Nat → α) (m : Nat) :
    (List.range (m + 1)).reverse.map f = ((List.range m).map Nat.succ).reverse.map f ++ [f 0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_append]
  rfl

theorem accum_tail (x tb p0 : BitVec 128) (A R : List (BitVec 128)) (hl : A.length = R.length) :
    accum (0, 0, 0) ((tailInputs x (A ++ [tb])).zip (R ++ [p0])) =
      accum (accum (0, 0, 0) ((tailInputs x A).zip (R ++ [p0]))) [((if A = [] then x else 0) ^^^ tb, p0)] := by
  cases A with
  | nil =>
    cases R with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a A =>
    have hl' : (tailInputs x (a :: A)).length = R.length := by rw [length_tailInputs]; exact hl
    rw [tailInputs_append _ _ _ (List.cons_ne_nil _ _), List.zip_append hl', accum_append,
      ← List.append_nil (tailInputs x (a :: A)), List.zip_append hl', List.append_nil, List.zip_nil_left,
      List.append_nil]
    simp

theorem powersDesc_split (t : low.x86_64.ghash.ClmulTable) (m : Nat) :
    powersDesc t (m + 1) =
      ((List.range m).map Nat.succ).reverse.map (fun i => t.powers.val[i]!) ++ [t.powers.val[0]!] :=
  range_succ_reverse _ m

theorem add_tail_eq (t : low.x86_64.ghash.ClmulTable) (H : P) (ht : TableFor H t) (bytes : List U8)
    (x : BitVec 128) (hb : bytes ≠ []) (hl : bytes.length ≤ 128) :
    low.x86_64.ghash.ClmulTable.add_tail t bytes x =
      ok (reduceAll ((tailInputs x (padBlocks bytes)).zip (powersDesc t ((bytes.length + 15) / 16)))) := by
  have hr := chunksRest_length 16 bytes
  have hm := chunksOf_length 16 bytes
  have hn8 : ¬ (bytes.length + 15) / 16 > 8 := by omega
  have hne : bytes.isEmpty = false := by simpa using hb
  have hps : ∀ p ∈ (List.range ((bytes.length + 15) / 16)).reverse.map
      (fun i => (t.powers.val[i]!, t.powers_xor.val[i]!)), p.2 = swap p.1 ^^^ p.1 := by
    intro p hp
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact (ht i (by omega)).2
  simp only [low.x86_64.ghash.ClmulTable.add_tail, hne, hn8,
    zip_take_reverse t _ (by omega : (bytes.length + 15) / 16 ≤ 8),
    Bool.false_eq_true, ite_false, core.core_arch.x86.sse2._mm_setzero_si128, bind_ok,
    add_tail_loop_eq x 0 0 0 (chunksOf 16 bytes) _ (by simp; omega) hps]
  have hfst : ∀ n, List.map Prod.fst (List.map (fun i => (t.powers.val[i]!, t.powers_xor.val[i]!))
      (List.range n).reverse) = powersDesc t n := fun n => by rw [List.map_map]; rfl
  simp only [hfst]
  by_cases h0 : bytes.length % 16 = 0
  · have hn : (bytes.length + 15) / 16 = (chunksOf 16 bytes).length := by omega
    have hrest : chunksRest 16 bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hd : List.drop (chunksOf 16 bytes).length (List.map (fun i => (t.powers.val[i]!, t.powers_xor.val[i]!))
        (List.range (chunksOf 16 bytes).length).reverse) = [] := by simp
    simp only [hn, hd, padBlocks, hrest, ite_true, List.append_nil, uncurry_apply_pair, bind_ok,
      reduce_model_eq, reduceAll]
  · have hn : (bytes.length + 15) / 16 = (chunksOf 16 bytes).length + 1 := by omega
    rw [hn] at hps ⊢
    have h00 := (ht 0 (by omega)).2
    simp only [range_succ_reverse, uncurry_apply_pair, bind_ok, low.x86_64.ghash.BYTESWAP, shuffle_byteswap,
      core.core_arch.x86.sse2._mm_xor_si128, h00]
    rw [List.drop_left' (by simp)]
    simp only [mul_model_eq, uncurry_apply_pair, bind_ok, reduce_model_eq]
    have hrest : chunksRest 16 bytes ≠ [] := fun h => h0 (by rw [← hr, h]; rfl)
    have hA : (List.map blockBE (chunksOf 16 bytes)).length =
        (((List.range (chunksOf 16 bytes).length).map Nat.succ).reverse.map (fun i => t.powers.val[i]!)).length := by
      simp
    simp only [padBlocks, hrest, ite_false, powersDesc_split, reduceAll]
    simp only [accum_tail _ _ _ _ _ hA, List.map_eq_nil_iff]
    rfl

theorem ghashPoly_append (H c : P) (l1 l2 : List P) :
    ghashPoly H c (l1 ++ l2) = ghashPoly H (ghashPoly H c l1) l2 := by
  rw [ghashPoly, ghashPoly, ghashPoly, List.foldl_append]

theorem padBlocks_nil : padBlocks [] = [] := by simp [padBlocks, chunksOf, chunksRest]

/-- `add_tail` hashes the padded blocks of up to 128 bytes. -/
theorem add_tail_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (bytes : List U8) (x : BitVec 128) (hl : bytes.length ≤ 128) :
    ∃ y, low.x86_64.ghash.ClmulTable.add_tail t bytes x = ok y ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes).map toPoly) := by
  by_cases hb : bytes = []
  · subst hb
    exact ⟨x, by simp [low.x86_64.ghash.ClmulTable.add_tail], by rw [padBlocks_nil, List.map_nil, ghashPoly_nil]⟩
  · refine ⟨_, add_tail_eq t H ht bytes x hb hl, ?_⟩
    have hlen := length_padBlocks bytes
    have hne : padBlocks bytes ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
      exact hb (List.eq_nil_of_length_eq_zero (by omega))
    have h := toPoly_reduceAll_powers H hH t ht (tailInputs x (padBlocks bytes))
      (by rw [length_tailInputs]; omega)
    rw [length_tailInputs, hlen] at h
    rw [h, sumPow_tailInputs H x _ hne]

/-! ## `add` -/

theorem chunksOf_append {α : Type} {k : Nat} (hk : 0 < k) : ∀ (j : Nat) (a b : List α), a.length = k * j →
    chunksOf k (a ++ b) = chunksOf k a ++ chunksOf k b
  | 0, a, b, h => by
    have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp [chunksOf]
  | j + 1, a, b, h => by
    have hka : k ≤ a.length := by rw [h, Nat.mul_succ]; omega
    rw [chunksOf_cons hk (by simp; omega), chunksOf_cons hk hka, List.take_append_of_le_length hka,
      List.drop_append_of_le_length hka,
      chunksOf_append hk j (a.drop k) b (by simp [h, Nat.mul_succ]), List.cons_append]

theorem chunksRest_append {α : Type} {k : Nat} (hk : 0 < k) : ∀ (j : Nat) (a b : List α), a.length = k * j →
    chunksRest k (a ++ b) = chunksRest k b
  | 0, a, b, h => by
    have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; rfl
  | j + 1, a, b, h => by
    have hka : k ≤ a.length := by rw [h, Nat.mul_succ]; omega
    rw [chunksRest_cons hk (by simp; omega), List.drop_append_of_le_length hka,
      chunksRest_append hk j (a.drop k) b (by simp [h, Nat.mul_succ])]

/-- A 128-byte chunk's blocks are its eight 16-byte ones. -/
theorem chunks_128 (bytes : List U8) :
    chunksOf 16 bytes = (chunksOf 128 bytes).flatMap (chunksOf 16) ++ chunksOf 16 (chunksRest 128 bytes) ∧
      chunksRest 16 bytes = chunksRest 16 (chunksRest 128 bytes) := by
  induction h : bytes.length using Nat.strong_induction_on generalizing bytes with
  | _ n ih =>
    by_cases hl : bytes.length < 128
    · simp [chunksOf_of_lt hl, chunksRest_of_lt hl]
    · have hl' : 128 ≤ bytes.length := by omega
      have h128 : (bytes.take 128).length = 16 * 8 := by simp; omega
      obtain ⟨ih1, ih2⟩ := ih (bytes.drop 128).length (by simp; omega) (bytes.drop 128) rfl
      have e := List.take_append_drop 128 bytes
      constructor
      · rw [chunksOf_cons (by omega) hl', chunksRest_cons (by omega) hl', List.flatMap_cons, List.append_assoc,
          ← ih1, ← chunksOf_append (by omega) 8 _ _ h128, e]
      · rw [chunksRest_cons (by omega) hl', ← ih2]
        conv_lhs => rw [← e]
        rw [chunksRest_append (by omega) 8 _ _ h128]

theorem padBlocks_128 (c : List U8) (hc : c.length = 128) : padBlocks c = (chunksOf 16 c).map blockBE := by
  have : chunksRest 16 c = [] := List.eq_nil_of_length_eq_zero (by rw [chunksRest_length, hc])
  simp [padBlocks, this]

theorem padBlocks_split (bytes : List U8) :
    padBlocks bytes = (chunksOf 128 bytes).flatMap padBlocks ++ padBlocks (chunksRest 128 bytes) := by
  obtain ⟨h1, h2⟩ := chunks_128 bytes
  have hflat : (chunksOf 128 bytes).flatMap padBlocks = ((chunksOf 128 bytes).flatMap (chunksOf 16)).map blockBE := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro c hc
    exact padBlocks_128 c (chunksOf_length_mem hc)
  rw [hflat, padBlocks, padBlocks, h1, h2, List.map_append, List.append_assoc]

theorem eight {α : Type} [Inhabited α] (l : List α) (h : l.length = 8) :
    l = [l[0]!, l[1]!, l[2]!, l[3]!, l[4]!, l[5]!, l[6]!, l[7]!] := by
  match l, h with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem add_loop_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t) :
    ∀ (chunks : List (List U8)) (x : BitVec 128), (∀ c ∈ chunks, c.length = 128) →
      ∃ y, low.x86_64.ghash.ClmulTable.add_loop t chunks x = ok y ∧
        toPoly y = ghashPoly H (toPoly x) ((chunks.flatMap padBlocks).map toPoly)
  | [], x, _ => ⟨x, rfl, by simp [ghashPoly_nil]⟩
  | c :: chunks, x, hc => by
    have hc0 : c.length = 128 := hc c (by simp)
    have h8 : (chunksOf 16 c).length = 8 := by rw [chunksOf_length, hc0]
    let y := reduceAll ((tailInputs x (padBlocks c)).zip (powersDesc t 8))
    have hy : low.x86_64.ghash.ClmulTable.add_loop t (c :: chunks) x =
        low.x86_64.ghash.ClmulTable.add_loop t chunks y := by
      rw [low.x86_64.ghash.ClmulTable.add_loop]
      simp only [load_be_eq, core.core_arch.x86.sse2._mm_xor_si128, bind_ok, mul8_eq H t ht]
      congr 2
      rw [padBlocks_128 c hc0, eight _ h8]
      rfl
    have hyp : toPoly y = ghashPoly H (toPoly x) ((padBlocks c).map toPoly) := by
      have hl : (padBlocks c).length = 8 := by rw [padBlocks_128 c hc0, List.length_map, h8]
      have hne : padBlocks c ≠ [] := fun h => by rw [h] at hl; simp at hl
      have h := toPoly_reduceAll_powers H hH t ht (tailInputs x (padBlocks c)) (by rw [length_tailInputs]; omega)
      rw [length_tailInputs, hl] at h
      rw [h, sumPow_tailInputs H x _ hne]
    obtain ⟨z, hz, hzp⟩ := add_loop_spec H hH t ht chunks y (fun c h => hc c (by simp [h]))
    exact ⟨z, hy ▸ hz, by rw [hzp, hyp, List.flatMap_cons, List.map_append, ghashPoly_append]⟩

/-- `ClmulTable::add` hashes the padded blocks of the bytes from the state
`x`, for a table of `H`'s powers. -/
theorem clmul_add_spec (H : P) (hH : Small H) (t : low.x86_64.ghash.ClmulTable) (ht : TableFor H t)
    (bytes : List U8) (x : BitVec 128) :
    ∃ y, low.x86_64.ghash.ClmulTable.add t bytes x = ok y ∧
      toPoly y = ghashPoly H (toPoly x) ((padBlocks bytes).map toPoly) := by
  obtain ⟨y, hy, hyp⟩ := add_loop_spec H hH t ht (chunksOf 128 bytes) x (fun c h => chunksOf_length_mem h)
  have hr : (chunksRest 128 bytes).length ≤ 128 := by rw [chunksRest_length]; omega
  obtain ⟨z, hz, hzp⟩ := add_tail_spec H hH t ht (chunksRest 128 bytes) y hr
  refine ⟨z, by rw [low.x86_64.ghash.ClmulTable.add, hy, bind_ok, hz], ?_⟩
  rw [hzp, hyp, padBlocks_split bytes, List.map_append, ghashPoly_append]

/-! ## The table `ClmulTable::new` builds -/

theorem gPower_add (H : P) (b : Nat) (hb : 1 ≤ b) : ∀ a, 1 ≤ a →
    gf128MulRev (gPower H a) (gPower H b) = gPower H (a + b)
  | 0, h => absurd h (by omega)
  | 1, _ => by rw [gPower_one, Nat.add_comm, gPower_succ H hb]
  | a + 2, _ => by
    rw [gPower_succ H (show 1 ≤ a + 1 by omega), mulRev_assoc, gPower_add H b hb (a + 1) (by omega),
      show a + 2 + b = (a + 1 + b) + 1 by omega, gPower_succ H (by omega)]

/-- `ClmulTable::powers`'s eight powers, from H to H^8, each shifted. -/
theorem ghashPowers_spec (h : BitVec 128) : ∀ i < 8,
    toPoly (ghashPowers h)[i]! = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) (i + 1)) := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := powers_spec h
  have s := small_gPower (toPoly h) (small_toPoly h)
  have p7 := mul_shiftKey1 _ _ (s 4) (s 3) _ _ p4 p3
  have p8 := mul_shiftKey1 _ _ (s 4) (s 4) _ _ p4 p4
  rw [gPower_add _ _ (by omega) _ (by omega)] at p7 p8
  intro i hi
  interval_cases i
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8

/-- `<[T; N]>::map`, for a closure that returns `g` of its argument. -/
theorem map_eq {T F U : Type} {N : Std.Usize} (inst : core.ops.function.FnMut F T U) (g : T → U)
    (hf : ∀ f x, inst.call_mut f x = ok (g x, f)) (a : Std.Array T N) (f : F) :
    ∃ h, core.array.Array.map inst a f = ok (Std.Array.from (a.val.map g) h) := by
  have key : ∀ (l : List T) (acc : List U), l.foldlM (fun (p : List U × F) x => do
      let (y, f) ← inst.call_mut p.2 x
      ok (p.1 ++ [y], f)) (acc, f) = ok (acc ++ l.map g, f) := by
    intro l
    induction l with
    | nil => intro acc; simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
    | cons x l ih =>
      intro acc
      have hy := hf f x
      simp only [List.foldlM_cons, hy, bind_ok, bind_tc_ok, uncurry_apply_pair]
      rw [ih]
      simp
  have hl : (a.val.map g).length = N.val := by rw [List.length_map, Std.Array.property]
  refine ⟨hl, ?_⟩
  unfold core.array.Array.map
  simp only [key, List.nil_append, bind_ok, uncurry_apply_pair]
  rw [dite_eq_left hl]

theorem clmul_new_spec (h : Std.U128) (hw : low.x86_64.cpu.HaveAesHardware) :
    ∃ t, low.x86_64.ghash.ClmulTable.new h hw = ok t ∧ TableFor (toPoly h.bv) t := by
  obtain ⟨hl, hm⟩ := map_eq
    low.x86_64.ghash.ClmulTable.with_powers.closure.Insts.CoreOpsFunctionFnMutTuple__m128i__m128i
    (fun p => swap p ^^^ p)
    (fun f x => by simp only [
      low.x86_64.ghash.ClmulTable.with_powers.closure.Insts.CoreOpsFunctionFnMutTuple__m128i__m128i.call_mut,
      low.x86_64.ghash.xor_halves, core.core_arch.x86.sse2._mm_shuffle_epi32,
      core.core_arch.x86.sse2._mm_xor_si128, bind_ok, swap_lanes])
    (Std.Array.make 8#usize (ghashPowers h.bv) (by simp [ghashPowers])) ()
  refine ⟨_, by simp only [low.x86_64.ghash.ClmulTable.new, powers_eq, bind_ok,
    low.x86_64.ghash.ClmulTable.with_powers, hm]; rfl, ?_⟩
  intro i hi
  refine ⟨ghashPowers_spec h.bv i hi, ?_⟩
  have hlen : i < (ghashPowers h.bv).length := by simp [ghashPowers]; omega
  rw [Std.Array.from_val, Std.Array.make_val, getElem!_pos _ i (by simpa using hlen),
    getElem!_pos _ i hlen, List.getElem_map]

/-! ## Vale's `ghash_LE` -/

/-- A Vale block or hash, its bytes least significant first, as the
polynomial rind's GHASH works on: of its bytes reversed. -/
noncomputable def polyLE (q : Quad32) : P := toPoly (reverseBytesQuad32 q)

theorem ofQuad32_eq (q : Quad32) : ofQuad32 q = toPoly q := rfl

theorem sum_two_pow_lt (b : Nat → Bool) : ∀ n, (∑ i ∈ Finset.range n, if b i then 2 ^ i else 0) < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Nat.pow_succ]
    have := sum_two_pow_lt b n
    split <;> omega

theorem testBit_sum (b : Nat → Bool) : ∀ n j,
    (∑ i ∈ Finset.range n, if b i then 2 ^ i else 0).testBit j = (decide (j < n) && b j)
  | 0, j => by simp
  | n + 1, j => by
    have hlt := sum_two_pow_lt b n
    have ih := testBit_sum b n j
    rw [Finset.sum_range_succ]
    by_cases hb : b n
    · rw [ite_eq_left hb, Nat.add_comm]
      rcases Nat.lt_trichotomy j n with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]; simp [h, show j < n + 1 by omega]
      · subst h; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp [hb]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 2 ^ n + _ < 2 ^ (n + 1) by rw [Nat.pow_succ]; omega)
          (Nat.pow_le_pow_right (by omega) h))]
        simp [show ¬ j < n + 1 by omega]
    · rw [ite_eq_right hb, Nat.add_zero, ih]
      by_cases h : j = n
      · subst h; simp [hb]
      · simp only [show (j < n + 1) = (j < n) by apply propext; omega]

theorem ofQuad32_toQuad32 {p : P} (hp : Small p) : ofQuad32 (toQuad32 p) = p := by
  ext j
  rw [ofQuad32_eq, coeff_toPoly, toQuad32, BitVec.getLsbD_ofNat]
  have hs := testBit_sum (fun i => decide (p.coeff i ≠ 0)) 128 j
  simp only [decide_eq_true_eq] at hs
  rw [hs]
  by_cases hj : j < 128
  · rcases zmod2_cases (p.coeff j) with h | h <;> simp [h, hj]
  · rw [hp.coeff (by omega)]; simp [hj]

theorem reverseBytes_xor (a b : Quad32) :
    reverseBytesQuad32 (a ^^^ b) = reverseBytesQuad32 a ^^^ reverseBytesQuad32 b := by
  apply eq_of_byte_eq; intro i hi
  rw [byte_xor, byte_reverseBytes _ hi, byte_reverseBytes _ hi, byte_reverseBytes _ hi, byte_xor]

theorem polyLE_xor (a b : Quad32) : polyLE (a ^^^ b) = polyLE a + polyLE b := by
  rw [polyLE, reverseBytes_xor, toPoly_xor]; rfl

theorem polyLE_zero : polyLE 0 = 0 := by
  have := polyLE_xor 0 0
  rw [BitVec.xor_self] at this
  have h2 : (2 : P) = 0 := two_eq_zero_P
  linear_combination this + polyLE 0 * h2

theorem polyLE_mulLE (a b : Quad32) : polyLE (gf128MulLE a b) = gf128MulRev (polyLE a) (polyLE b) := by
  rw [polyLE, gf128MulLE]
  simp only [reverseBytesQuad32_involutive]
  rw [← ofQuad32_eq]
  exact ofQuad32_toQuad32 (small_mulRev _ _)

theorem polyLE_foldl (h : Quad32) : ∀ (xs : List Quad32) (y : Quad32),
    polyLE (xs.foldl (fun y xi => gf128MulLE (y ^^^ xi) h) y) = ghashPoly (polyLE h) (polyLE y) (xs.map polyLE)
  | [], y => by rw [List.foldl_nil, List.map_nil, ghashPoly_nil]
  | x :: xs, y => by
    rw [List.foldl_cons, polyLE_foldl h xs, polyLE_mulLE, polyLE_xor, List.map_cons, ghashPoly_cons]

/-- Vale's `ghash_LE` is GHASH from zero on the blocks' polynomials. -/
theorem polyLE_ghashLE (h : Quad32) (xs : List Quad32) :
    polyLE (ghashLE h xs) = ghashPoly (polyLE h) 0 (xs.map polyLE) := by
  rw [ghashLE, polyLE_foldl, polyLE_zero]

/-! ## Vale's padded blocks -/

theorem chunksOf_map {α β : Type} (f : α → β) (k : Nat) (l : List α) :
    chunksOf k (l.map f) = (chunksOf k l).map (List.map f) := by
  simp [chunksOf, List.map_take, List.map_drop]

theorem getElem!_take_drop {α : Type} [Inhabited α] (l : List α) (a c j : Nat) (hj : j < c) :
    ((l.drop a).take c)[j]! = l[a + j]! := by
  simp [getElem!_def, List.getElem?_drop, hj]

theorem leBytesToSeqQuad32_eq (b : List (BitVec 8)) :
    leBytesToSeqQuad32 b = (chunksOf 16 b).map leBytesToQuad32 := by
  unfold leBytesToSeqQuad32 seqToSeqFourLE chunksOf
  have hw : (seqNat8ToSeqNat32LE b).length = b.length / 4 := by simp [seqNat8ToSeqNat32LE]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hw, Nat.div_div_eq_div_mul]
  · intro n h1 _
    simp only [List.length_map, List.length_range, hw, Nat.div_div_eq_div_mul] at h1
    simp only [List.getElem_map, List.getElem_range]
    apply eq_of_byte_eq; intro i hi
    rw [byte_mkfour _ _ _ _ hi, byte_leBytesToQuad32 _ hi, getElem!_take_drop _ _ _ _ hi]
    have hword : ∀ k, k < b.length / 4 → ∀ m, m < 4 →
        wbyte (seqNat8ToSeqNat32LE b)[k]! m = b[4 * k + m]! := by
      intro k hk m hm
      rw [seqNat8ToSeqNat32LE, getElem!_range_map _ hk, wbyte, byte_word _ hm, getElem!_take_drop _ _ _ _ hm]
    have hk : ∀ j, j < 4 → n * 4 + j < b.length / 4 := fun j hj => by
      have : n * 16 + 16 ≤ b.length := by
        have := Nat.mul_le_of_le_div 16 (n + 1) b.length (by omega); linarith
      omega
    by_cases a1 : i < 4
    · rw [ite_eq_left a1, hword (n * 4) (by have := hk 0 (by omega); omega) _ (by omega)]; congr 1; omega
    by_cases a2 : i < 8
    · rw [ite_eq_right a1, ite_eq_left a2, hword (n * 4 + 1) (hk 1 (by omega)) _ (by omega)]; congr 1; omega
    by_cases a3 : i < 12
    · rw [ite_eq_right a1, ite_eq_right a2, ite_eq_left a3, hword (n * 4 + 2) (hk 2 (by omega)) _ (by omega)]; congr 1; omega
    · rw [ite_eq_right a1, ite_eq_right a2, ite_eq_right a3, hword (n * 4 + 3) (hk 3 (by omega)) _ (by omega)]; congr 1; omega

theorem chunksOf_16 {α : Type} (l : List α) (h : l.length = 16) : chunksOf 16 l = [l] := by
  rw [chunksOf_cons (by omega) (by omega), List.take_of_length_le (by omega),
    chunksOf_of_lt (by simp; omega)]

/-- Vale's zero-padded blocks of the bytes, as polynomials, are `padBlocks`'s. -/
theorem padBlocks_vale (bytes : List U8) :
    (leBytesToSeqQuad32 (padTo128Bits (bytes.map (·.bv)))).map polyLE = (padBlocks bytes).map toPoly := by
  have hsplit := List.take_append_drop (16 * (bytes.length / 16)) bytes
  have hA : (bytes.take (16 * (bytes.length / 16))).length = 16 * (bytes.length / 16) := by
    simp; have := Nat.div_mul_le_self bytes.length 16; omega
  have hr := chunksRest_length 16 bytes
  have hR : (bytes.drop (16 * (bytes.length / 16))).length = bytes.length % 16 := hr
  have hc : chunksOf 16 bytes = chunksOf 16 (bytes.take (16 * (bytes.length / 16))) := by
    conv_lhs => rw [← hsplit]
    rw [chunksOf_append (by omega) _ _ _ hA,
      chunksOf_of_lt (l := bytes.drop (16 * (bytes.length / 16))) (by omega), List.append_nil]
  have hbv : bytes.map (·.bv) = (bytes.take (16 * (bytes.length / 16))).map (·.bv) ++
      (bytes.drop (16 * (bytes.length / 16))).map (·.bv) := by
    rw [← List.map_append, hsplit]
  rw [leBytesToSeqQuad32_eq, padTo128Bits, padBlocks, List.length_map]
  split
  · rename_i h0
    have hrest : chunksRest 16 bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [hrest, ite_true, List.append_nil, chunksOf_map, List.map_map]
    rfl
  · rename_i h0
    have hrest : chunksRest 16 bytes ≠ [] := fun h => h0 (by rw [← hr, h]; rfl)
    rw [ite_eq_right hrest, hbv, List.append_assoc,
      chunksOf_append (by omega) (bytes.length / 16) _ _ (by rw [List.length_map, hA]),
      chunksOf_16 ((bytes.drop (16 * (bytes.length / 16))).map (·.bv) ++ List.replicate (16 - bytes.length % 16) 0)
        (by simp only [List.length_append, List.length_map, List.length_replicate, hR]; omega),
      chunksOf_map, ← hc]
    have hb : ∀ c : List U8, polyLE (leBytesToQuad32 (c.map (·.bv))) = toPoly (blockBE c) := fun _ => rfl
    have ht : polyLE (leBytesToQuad32 ((bytes.drop (16 * (bytes.length / 16))).map (·.bv) ++
        List.replicate (16 - bytes.length % 16) 0)) = toPoly (tailBlock (chunksRest 16 bytes)) := by
      rw [tailBlock, ← hb, hr, List.map_append, List.map_replicate]
      rfl
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def, hb, ht]

end rind.x86_64

