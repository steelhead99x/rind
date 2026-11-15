module
public import Rind.Lanes
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.unusedSimpArgs false

/-!
# A constant-time row select over 128-bit vectors

rind's point selects scan a table of `N`-word rows, comparing a 32-bit
counter with the index in every lane and accumulating each row's words under
the mask: SSE2's and AVX2's on x86_64 (`Rind.X86_64.PointSelect`) and NEON's on
aarch64 (`Rind.Aarch64.PointSelect`). These are the facts about 128-bit vectors,
the counter, and the table's rows those proofs share.
-/

namespace rind.select

open rind.simd

/-- Row `index` of a table of `N`-word rows, counting from 1, or `N` zero
words where there is none. -/
def tableRow (N : Nat) (table : List U64) (index : Nat) : List U64 :=
  if 1 ≤ index ∧ index ≤ table.length / N then (table.drop (N * (index - 1))).take N
  else List.replicate N 0#u64

/-- The two words of `row` from `row[k]`, as an unaligned 128-bit load reads
them: `row[k]` lowest. -/
def load128 (row : List U64) (k : Nat) : BitVec 128 :=
  (row.getD (k + 1) 0#u64).bv ++ (row.getD k 0#u64).bv

/-- A 128-bit vector's words, as a 128-bit store writes them: lane 0 first. -/
def store128 (v : BitVec 128) : List U64 :=
  (List.range 2).map fun j => ⟨v.extractLsb' (64 * j) 64⟩

/-! ## Lanes -/

theorem lane32_ofLanes32 (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    lane32 (ofLanes32 f) i = f i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp only [lane32, ofLanes32] <;>
    (repeat (rw [BitVec.extractLsb'_append_eq_of_le (by omega)])) <;>
    first | exact BitVec.extractLsb'_append_eq_right | exact BitVec.extractLsb'_eq_self

theorem ofLanes32_congr {f g : Nat → BitVec 32} (h : ∀ i < 4, f i = g i) :
    ofLanes32 f = ofLanes32 g := by
  simp only [ofLanes32, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem ofLanes32_allOnes : ofLanes32 (fun _ => BitVec.allOnes 32) = BitVec.allOnes 128 := by
  decide

theorem ofLanes32_zero : ofLanes32 (fun _ => 0#32) = 0#128 := by
  decide

/-- A 32-bit lanewise compare of two broadcasts. -/
theorem cmpeq128_bcast (a b : BitVec 32) :
    ofLanes32 (fun i => if lane32 (ofLanes32 fun _ => a) i = lane32 (ofLanes32 fun _ => b) i
      then BitVec.allOnes 32 else 0) = if a = b then BitVec.allOnes 128 else 0 := by
  rw [ofLanes32_congr (g := fun _ => if a = b then BitVec.allOnes 32 else 0)
    (fun i hi => by rw [lane32_ofLanes32 _ hi, lane32_ofLanes32 _ hi])]
  split
  · exact ofLanes32_allOnes
  · exact ofLanes32_zero

/-- A 32-bit lanewise sum of two broadcasts. -/
theorem add128_bcast (a b : BitVec 32) :
    ofLanes32 (fun i => lane32 (ofLanes32 fun _ => a) i + lane32 (ofLanes32 fun _ => b) i) =
      ofLanes32 fun _ => a + b :=
  ofLanes32_congr fun i hi => by rw [lane32_ofLanes32 _ hi, lane32_ofLanes32 _ hi]

/-- A masked word: all of it under an all-ones mask, none under zero. -/
theorem and_mask {w : Nat} (x : BitVec w) (c : Prop) [Decidable c] :
    (x &&& if c then BitVec.allOnes w else 0) = if c then x else 0 := by
  split <;> simp

/-- The counter after `r` rows matches the 8-bit index exactly where `r + 1`
is the index, while the counter does not wrap. -/
theorem counter_eq (r : Nat) (index : U8) (hr : r + 1 < 2 ^ 32) :
    (1#32 + BitVec.ofNat 32 r = index.bv.setWidth 32) ↔ r + 1 = index.val := by
  have hi : index.val < 256 := by have := index.hBounds; simpa [UScalarTy.numBits] using this
  have e : (index.bv.setWidth 32).toNat = index.val := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by simp only [UScalar.val] at hi; omega)
  rw [← BitVec.toNat_inj, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e,
    Nat.mod_eq_of_lt (show 1 < 2 ^ 32 by decide), Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show 1 + r < 2 ^ 32 by omega)]
  constructor <;> intro h <;> omega

theorem counter_succ (k : Nat) :
    (1#32 + BitVec.ofNat 32 k) + 1#32 = 1#32 + BitVec.ofNat 32 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Loads and stores -/

theorem store128_load128 (row : List U64) (k : Nat) :
    store128 (load128 row k) = [row.getD k 0#u64, row.getD (k + 1) 0#u64] := by
  simp only [store128, load128, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  · rw [Nat.mul_zero, BitVec.extractLsb'_append_eq_right]
  · rw [Nat.mul_one, BitVec.extractLsb'_append_eq_left]

theorem store128_zero : store128 (0 : BitVec 128) = List.replicate 2 0#u64 := by decide

theorem take_add_getD (l : List U64) (n : Nat) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.getD n 0#u64] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  rfl

theorem flatMap_store128 (row : List U64) : ∀ (V : Nat), 2 * V ≤ row.length →
    (List.range V).flatMap (fun i => store128 (load128 row (2 * i))) = row.take (2 * V)
  | 0, _ => by simp
  | V + 1, h => by
    rw [List.range_succ, List.flatMap_append, flatMap_store128 row V (by omega), List.flatMap_singleton,
      store128_load128, show 2 * (V + 1) = 2 * V + 1 + 1 by omega,
      take_add_getD _ _ (by omega), take_add_getD _ _ (by omega)]
    simp

theorem flatMap_replicate {α : Type} (x : α) (k : Nat) : ∀ (V : Nat),
    (List.range V).flatMap (fun _ => List.replicate k x) = List.replicate (k * V) x
  | 0 => by simp
  | V + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_replicate x k V, List.flatMap_singleton,
      Nat.mul_succ, List.replicate_add]

theorem mapM_ok {α β : Type} (f : α → β) : ∀ (l : List α), l.mapM (fun a => ok (f a)) = ok (l.map f)
  | [] => rfl
  | a :: l => by simp only [List.mapM_cons, mapM_ok f l, bind_tc_ok, pure_tc_eq, List.map_cons]

theorem getD_map_range {α : Type} (g : Nat → α) (d : α) {V i : Nat} (hi : i < V) :
    ((List.range V).map g).getD i d = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- 128-bit stores, once the accumulators hold a row's words, write that
row. -/
theorem out128 (row : List U64) (V : Nat) (hlen : row.length = 2 * V) :
    ((List.range V).map fun i => load128 row (2 * i)).flatMap store128 = row := by
  rw [List.flatMap_map, flatMap_store128 row V (by omega), List.take_of_length_le (by omega)]

/-- 128-bit stores of zeroed accumulators write zeros. -/
theorem out128_zero (V : Nat) :
    ((List.range V).map fun _ => (0 : BitVec 128)).flatMap store128 = List.replicate (2 * V) 0#u64 := by
  rw [List.flatMap_map, store128_zero, flatMap_replicate, Nat.mul_comm]

/-! ## The table's rows -/

section
variable (N : Nat) (table : List U64) (index : U8)

/-- Row `r` of the table, from 0. -/
def row (r : Nat) : List U64 := (table.drop (N * r)).take N

/-- The row the select picks is among the first `k`. -/
def picked (k : Nat) : Prop := 1 ≤ index.val ∧ index.val ≤ k

instance (k : Nat) : Decidable (picked index k) := by unfold picked; infer_instance

theorem picked_succ {k : Nat} (hk : k + 1 ≠ index.val) : picked index (k + 1) ↔ picked index k := by
  unfold picked; omega

theorem picked_at {k : Nat} (hk : k + 1 = index.val) :
    picked index index.val ∧ ¬picked index k ∧ index.val - 1 = k := by
  unfold picked; omega

theorem picked_zero : ¬picked index 0 := by unfold picked; omega

theorem row_length {r : Nat} (hr : r < table.length / N) : (row N table r).length = N := by
  have h1 : (r + 1) * N ≤ table.length / N * N := Nat.mul_le_mul_right N hr
  have h2 := Nat.div_mul_le_self table.length N
  simp only [row, List.length_take, List.length_drop]
  rw [Nat.succ_mul, Nat.mul_comm r N] at h1
  generalize table.length / N * N = m at h1 h2
  generalize N * r = a at h1 ⊢
  omega

theorem tableRow_eq : tableRow N table index.val =
    if picked index (table.length / N) then row N table (index.val - 1) else List.replicate N 0#u64 := by
  simp [tableRow, picked, row]

end

end rind.select
