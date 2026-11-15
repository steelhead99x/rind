module
public import Rind.X86_64.FunsExternal
public import Rind.RowSelect
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false

/-!
# x86_64's point select, proven

`select_avx2_spec` and `select_sse2_spec` prove that
`Rind.X86_64.PointSelectModel`'s model of `select_avx2::<N, V>` and
`select_sse2::<N, V>` returns row `index` of a table of `N`-word rows, counting
from 1, or zeros for an index of 0 or past the last row, for every `N` their
`const` assertions admit and every table of fewer than 2^32 rows, whose 32-bit
counters do not wrap. So `bignum_aff_point_select_p256`, `_p384`, and `_p521`
select the same row whichever path `HaveAvx2::check` picks, under
`RunsSelect`, that the check returns.
-/

namespace rind.x86_64

open rind.simd rind.select

/-- The selects' dispatch runs: `HaveAvx2::check` returns. -/
def RunsSelect : Prop := ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t

/-! ## Lanes -/

theorem lane32x8_ofLanes32x8 (f : Nat → BitVec 32) {i : Nat} (hi : i < 8) :
    lane32x8 (ofLanes32x8 f) i = f i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [lane32x8, ofLanes32x8] <;>
    (repeat (rw [BitVec.extractLsb'_append_eq_of_le (by omega)])) <;>
    first | exact BitVec.extractLsb'_append_eq_right | exact BitVec.extractLsb'_eq_self

theorem ofLanes32x8_congr {f g : Nat → BitVec 32} (h : ∀ i < 8, f i = g i) :
    ofLanes32x8 f = ofLanes32x8 g := by
  simp only [ofLanes32x8, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]

theorem ofLanes32x8_allOnes : ofLanes32x8 (fun _ => BitVec.allOnes 32) = BitVec.allOnes 256 := by
  decide

theorem ofLanes32x8_zero : ofLanes32x8 (fun _ => 0#32) = 0#256 := by
  decide

/-- `_mm256_cmpeq_epi32` of two broadcasts. -/
theorem cmpeq256_bcast (a b : BitVec 32) :
    ofLanes32x8 (fun i => if lane32x8 (ofLanes32x8 fun _ => a) i = lane32x8 (ofLanes32x8 fun _ => b) i
      then BitVec.allOnes 32 else 0) = if a = b then BitVec.allOnes 256 else 0 := by
  rw [ofLanes32x8_congr (g := fun _ => if a = b then BitVec.allOnes 32 else 0)
    (fun i hi => by rw [lane32x8_ofLanes32x8 _ hi, lane32x8_ofLanes32x8 _ hi])]
  split
  · exact ofLanes32x8_allOnes
  · exact ofLanes32x8_zero

/-- `_mm256_add_epi32` of two broadcasts. -/
theorem add256_bcast (a b : BitVec 32) :
    ofLanes32x8 (fun i => lane32x8 (ofLanes32x8 fun _ => a) i + lane32x8 (ofLanes32x8 fun _ => b) i) =
      ofLanes32x8 fun _ => a + b :=
  ofLanes32x8_congr fun i hi => by rw [lane32x8_ofLanes32x8 _ hi, lane32x8_ofLanes32x8 _ hi]

theorem setWidth_allOnes : (BitVec.allOnes 256).setWidth 128 = BitVec.allOnes 128 := by decide

theorem setWidth_zero256 : (0 : BitVec 256).setWidth 128 = 0 := by decide

theorem setWidth_mask (c : Prop) [Decidable c] :
    (if c then BitVec.allOnes 256 else 0#256).setWidth 128 = if c then BitVec.allOnes 128 else 0 := by
  split <;> decide

theorem mm256_cmpeq_bcast (a b : BitVec 32) :
    core.core_arch.x86.avx2._mm256_cmpeq_epi32 (ofLanes32x8 fun _ => a) (ofLanes32x8 fun _ => b) =
      ok (if a = b then BitVec.allOnes 256 else 0) := by
  unfold core.core_arch.x86.avx2._mm256_cmpeq_epi32; rw [cmpeq256_bcast]

theorem mm_cmpeq_bcast (a b : BitVec 32) :
    core.core_arch.x86.sse2._mm_cmpeq_epi32 (ofLanes32 fun _ => a) (ofLanes32 fun _ => b) =
      ok (if a = b then BitVec.allOnes 128 else 0) := by
  unfold core.core_arch.x86.sse2._mm_cmpeq_epi32; rw [cmpeq128_bcast]

theorem mm256_add_bcast (a b : BitVec 32) :
    core.core_arch.x86.avx2._mm256_add_epi32 (ofLanes32x8 fun _ => a) (ofLanes32x8 fun _ => b) =
      ok (ofLanes32x8 fun _ => a + b) := by
  unfold core.core_arch.x86.avx2._mm256_add_epi32; rw [add256_bcast]

theorem mm_add_bcast (a b : BitVec 32) :
    core.core_arch.x86.sse2._mm_add_epi32 (ofLanes32 fun _ => a) (ofLanes32 fun _ => b) =
      ok (ofLanes32 fun _ => a + b) := by
  unfold core.core_arch.x86.sse2._mm_add_epi32; rw [add128_bcast]

/-! ## Loads and stores -/

theorem store256_load256 (row : List U64) (k : Nat) :
    store256 (load256 row k) = [row.getD k 0#u64, row.getD (k + 1) 0#u64, row.getD (k + 2) 0#u64,
      row.getD (k + 3) 0#u64] := by
  simp only [store256, load256, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩
  · rw [Nat.mul_zero, BitVec.extractLsb'_append_eq_right]
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega), show 64 * 1 - 64 = 0 by rfl,
      BitVec.extractLsb'_append_eq_right]
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      show 64 * 2 - 64 - 64 = 0 by rfl, BitVec.extractLsb'_append_eq_right]
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega), show 64 * 3 - 64 - 64 - 64 = 0 by rfl,
      BitVec.extractLsb'_eq_self]

theorem store256_zero : store256 (0 : BitVec 256) = List.replicate 4 0#u64 := by decide

theorem flatMap_store256 (row : List U64) : ∀ (V : Nat), 4 * V ≤ row.length →
    (List.range V).flatMap (fun i => store256 (load256 row (4 * i))) = row.take (4 * V)
  | 0, _ => by simp
  | V + 1, h => by
    rw [List.range_succ, List.flatMap_append, flatMap_store256 row V (by omega), List.flatMap_singleton,
      store256_load256, show 4 * (V + 1) = 4 * V + 1 + 1 + 1 + 1 by omega,
      take_add_getD _ _ (by omega), take_add_getD _ _ (by omega), take_add_getD _ _ (by omega),
      take_add_getD _ _ (by omega)]
    simp

/-! ## The loops -/

section
variable (N : Nat) (table : List U64) (index : U8)

/-- `_select_avx2`'s state after `k` rows. -/
def avx2After (V k : Nat) : Avx2State :=
  (ofLanes32x8 fun _ => 1#32 + BitVec.ofNat 32 k,
    (List.range V).map fun i => if picked index k then load256 (row N table (index.val - 1)) (4 * i) else 0,
    if N > 4 * V ∧ picked index k then load128 (row N table (index.val - 1)) (4 * V) else 0)

/-- `select_sse2`'s state after `k` rows. -/
def sse2After (V k : Nat) : core.core_arch.x86.__m128i × List core.core_arch.x86.__m128i :=
  (ofLanes32 fun _ => 1#32 + BitVec.ofNat 32 k,
    (List.range V).map fun i => if picked index k then load128 (row N table (index.val - 1)) (2 * i) else 0)

theorem avx2_row_step (V k : Nat) (hk : k + 1 < 2 ^ 32) :
    low.x86_64.bignum_point_select.select_avx2_row N V
      (ofLanes32x8 fun _ => index.bv.setWidth 32) (ofLanes32x8 fun _ => 1#32)
      (avx2After N table index V k) (row N table k) = ok (avx2After N table index V (k + 1)) := by
  simp only [low.x86_64.bignum_point_select.select_avx2_row, avx2After,
    mm256_cmpeq_bcast, mm256_add_bcast,
    core.core_arch.x86.avx2._mm256_and_si256, core.core_arch.x86.avx2._mm256_xor_si256,
    core.core_arch.x86.avx._mm256_castsi256_si128, core.core_arch.x86.sse2._mm_and_si128,
    core.core_arch.x86.sse2._mm_xor_si128, bind_ok, mapM_ok,
    and_mask, counter_eq k index hk, counter_succ]
  by_cases hk' : k + 1 = index.val
  · obtain ⟨h1, h2, h3⟩ := picked_at index hk'
    by_cases hN : N > 4 * V <;>
    · simp only [hk', h1, h2, h3, hN, ite_true, ite_false, true_and, false_and, and_true, and_false,
        bind_ok, bind_tc_ok, setWidth_allOnes, BitVec.and_allOnes, BitVec.zero_xor]
      refine congrArg ok (Prod.ext rfl (Prod.ext ?_ ?_))
      · apply List.map_congr_left
        intro i hi
        rw [getD_map_range _ _ (List.mem_range.mp hi)]
        simp [h1, h2]
      · simp [h1, h2, hN]
  · have h1 := picked_succ index hk'
    by_cases hN : N > 4 * V <;>
    · simp only [hk', h1, hN, ite_true, ite_false, true_and, false_and, and_true, and_false, bind_ok,
        bind_tc_ok, setWidth_zero256, BitVec.and_zero, BitVec.xor_zero]
      refine congrArg ok (Prod.ext rfl (Prod.ext ?_ ?_))
      · apply List.map_congr_left
        intro i hi
        rw [getD_map_range _ _ (List.mem_range.mp hi)]
        simp
      · simp [h1, hN, setWidth_zero256]

theorem sse2_row_step (V k : Nat) (hk : k + 1 < 2 ^ 32) :
    low.x86_64.bignum_point_select.select_sse2_row V
      (ofLanes32 fun _ => index.bv.setWidth 32) (ofLanes32 fun _ => 1#32)
      (sse2After N table index V k) (row N table k) = ok (sse2After N table index V (k + 1)) := by
  simp only [low.x86_64.bignum_point_select.select_sse2_row, sse2After,
    mm_cmpeq_bcast, mm_add_bcast,
    core.core_arch.x86.sse2._mm_and_si128, core.core_arch.x86.sse2._mm_xor_si128, bind_ok, mapM_ok, and_mask, counter_eq k index hk, counter_succ]
  by_cases hk' : k + 1 = index.val
  · obtain ⟨h1, h2, h3⟩ := picked_at index hk'
    simp only [hk', h1, h3, ite_true, BitVec.and_allOnes, bind_tc_ok]
    refine congrArg ok (Prod.ext rfl ?_)
    apply List.map_congr_left
    intro i hi
    rw [getD_map_range _ _ (List.mem_range.mp hi)]
    simp [h1, h2]
  · have h1 := picked_succ index hk'
    simp only [hk', h1, ite_false, BitVec.and_zero, BitVec.xor_zero, bind_tc_ok]
    refine congrArg ok (Prod.ext rfl ?_)
    apply List.map_congr_left
    intro i hi
    rw [getD_map_range _ _ (List.mem_range.mp hi)]
    simp

theorem avx2_loop (V : Nat) : ∀ k, k < 2 ^ 32 →
    (List.range k).foldlM (fun st r => low.x86_64.bignum_point_select.select_avx2_row N V
      (ofLanes32x8 fun _ => index.bv.setWidth 32) (ofLanes32x8 fun _ => 1#32) st (row N table r))
      (avx2After N table index V 0) = ok (avx2After N table index V k)
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [List.range_succ, List.foldlM_append, avx2_loop V k (by omega), bind_tc_ok,
      List.foldlM_cons, avx2_row_step N table index V k hk, List.foldlM_nil, pure_tc_eq]

theorem sse2_loop (V : Nat) : ∀ k, k < 2 ^ 32 →
    (List.range k).foldlM (fun st r => low.x86_64.bignum_point_select.select_sse2_row V
      (ofLanes32 fun _ => index.bv.setWidth 32) (ofLanes32 fun _ => 1#32) st (row N table r))
      (sse2After N table index V 0) = ok (sse2After N table index V k)
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [List.range_succ, List.foldlM_append, sse2_loop V k (by omega), bind_tc_ok,
      List.foldlM_cons, sse2_row_step N table index V k hk, List.foldlM_nil, pure_tc_eq]

theorem chunksOf_eq_row : chunksOf N table = (List.range (table.length / N)).map (row N table) := rfl

theorem avx2After_zero (V : Nat) :
    avx2After N table index V 0 = ((ofLanes32x8 fun _ => 1#32), List.replicate V 0, 0) := by
  have hp : ¬picked index 0 := by unfold picked; omega
  have h1 : 1#32 + BitVec.ofNat 32 0 = 1#32 := by decide
  simp only [avx2After, hp, h1, ite_false, and_false, List.map_const', List.length_range]

theorem sse2After_zero (V : Nat) :
    sse2After N table index V 0 = ((ofLanes32 fun _ => 1#32), List.replicate V 0) := by
  have hp : ¬picked index 0 := by unfold picked; omega
  have h1 : 1#32 + BitVec.ofNat 32 0 = 1#32 := by decide
  simp only [sse2After, hp, h1, ite_false, List.map_const', List.length_range]

end

/-! ## The selects -/

/-- `select_avx2`'s stores, once the accumulators and tail hold a row's
words, write that row. -/
theorem avx2_out (row : List U64) (N V : Nat) (hN : N = 4 * V ∨ N = 4 * V + 2)
    (hlen : row.length = N) (tail : core.core_arch.x86.__m128i)
    (htail : N > 4 * V → tail = load128 row (4 * V)) :
    ((List.range V).map fun i => load256 row (4 * i)).flatMap store256 ++
      (if N > 4 * V then store128 tail else []) = row := by
  rw [List.flatMap_map, flatMap_store256 row V (by omega)]
  rcases hN with h | h
  · rw [ite_eq_right (by omega), List.append_nil, List.take_of_length_le (by omega)]
  · rw [ite_eq_left (by omega), htail (by omega), store128_load128, ← List.singleton_append, ← List.append_assoc,
      ← take_add_getD _ _ (by omega), ← List.append_nil [row.getD (4 * V + 1) 0#u64],
      List.singleton_append, ← take_add_getD _ _ (by omega), List.take_of_length_le (by omega)]

/-- `select_avx2`'s stores of zeroed accumulators and tail write zeros. -/
theorem avx2_out_zero (N V : Nat) (hN : N = 4 * V ∨ N = 4 * V + 2) :
    ((List.range V).map fun _ => (0 : core.core_arch.x86.__m256i)).flatMap store256 ++
      (if N > 4 * V then store128 0 else []) = List.replicate N 0#u64 := by
  rw [List.flatMap_map, store256_zero, flatMap_replicate]
  rcases hN with h | h
  · rw [ite_eq_right (by omega), List.append_nil, h, Nat.mul_comm]
  · rw [ite_eq_left (by omega), store128_zero, ← List.replicate_add, h, Nat.mul_comm]

theorem i32_mk_bv (x : BitVec 32) : (⟨x⟩ : Std.I32).bv = x := rfl

theorem one_i32_bv : (1#i32 : Std.I32).bv = 1#32 := rfl

theorem select_avx2_spec (N : Std.Usize) (V : Nat) (h0 : 0 < N.val)
    (hN : N.val = 4 * V ∨ N.val = 4 * V + 2)
    (z : Std.Array U64 N) (table : Slice U64) (index : U8) (token : low.x86_64.cpu.HaveAvx2)
    (hrows : table.length / N.val < 2 ^ 32) :
    low.x86_64.bignum_point_select.select_avx2 N V z table index token ⦃ r =>
      r.val = tableRow N.val table.val index.val ⦄ := by
  unfold low.x86_64.bignum_point_select.select_avx2
  rw [ite_eq_left ⟨h0, hN⟩]
  have hrows' : table.val.length / N.val < 2 ^ 32 := hrows
  have hloop := avx2_loop N.val table.val index V _ hrows'
  rw [avx2After_zero] at hloop
  simp only [core.core_arch.x86.avx._mm256_setzero_si256, core.core_arch.x86.sse2._mm_setzero_si128,
    core.core_arch.x86.avx._mm256_set1_epi32, bind_ok, bind_tc_ok, chunksOf_eq_row, List.foldlM_map,
    i32_mk_bv, one_i32_bv]
  rw [hloop]
  simp only [bind_ok, bind_tc_ok, avx2After]
  rw [tableRow_eq]
  by_cases hp : picked index (table.val.length / N.val)
  · have hlen := row_length N.val table.val (r := index.val - 1) (by unfold picked at hp; omega)
    simp only [hp, ite_true, and_true]
    simp only [avx2_out _ _ _ hN hlen _ (fun h => ite_eq_left h)]
    rw [dite_eq_left hlen, WP.spec_ok, Array.from_val]
  · simp only [hp, ite_false, and_false, avx2_out_zero N.val V hN]
    rw [dite_eq_left (List.length_replicate ..), WP.spec_ok, Array.from_val]

theorem select_sse2_spec (N : Std.Usize) (V : Nat) (h0 : 0 < N.val) (hN : N.val = 2 * V)
    (z : Std.Array U64 N) (table : Slice U64) (index : U8)
    (hrows : table.length / N.val < 2 ^ 32) :
    low.x86_64.bignum_point_select.select_sse2 N V z table index ⦃ r =>
      r.val = tableRow N.val table.val index.val ⦄ := by
  unfold low.x86_64.bignum_point_select.select_sse2
  rw [ite_eq_left ⟨h0, hN⟩]
  have hrows' : table.val.length / N.val < 2 ^ 32 := hrows
  have hloop := sse2_loop N.val table.val index V _ hrows'
  rw [sse2After_zero] at hloop
  simp only [core.core_arch.x86.sse2._mm_setzero_si128, core.core_arch.x86.sse2._mm_set1_epi32,
    bind_ok, bind_tc_ok, chunksOf_eq_row, List.foldlM_map, i32_mk_bv, one_i32_bv]
  rw [hloop]
  simp only [bind_ok, bind_tc_ok, sse2After]
  rw [tableRow_eq]
  by_cases hp : picked index (table.val.length / N.val)
  · have hlen := row_length N.val table.val (r := index.val - 1) (by unfold picked at hp; omega)
    simp only [hp, ite_true]
    have hlen2 : (row N.val table.val (index.val - 1)).length = 2 * V := by rw [hlen, hN]
    simp only [out128 _ V hlen2]
    rw [dite_eq_left hlen, WP.spec_ok, Array.from_val]
  · simp only [hp, ite_false, out128_zero V, ← hN]
    rw [dite_eq_left (List.length_replicate ..), WP.spec_ok, Array.from_val]

/-! ## The dispatch -/

/-- `bignum_aff_point_select_p256` returns row `index` of P-256's table of
8-word affine points, or zeros. -/
@[step]
theorem bignum_aff_point_select_p256_spec (hc : RunsSelect) (z : Std.Array U64 8#usize)
    (table : Slice U64) (index : U8) (hrows : table.length / 8 < 2 ^ 32) :
    low.x86_64.bignum_point_select.bignum_aff_point_select_p256 z table index ⦃ r =>
      r.val = tableRow 8 table.val index.val ⦄ := by
  obtain ⟨t, ht⟩ := hc
  unfold low.x86_64.bignum_point_select.bignum_aff_point_select_p256
  simp only [ht, bind_ok, bind_tc_ok]
  cases t with
  | some token => exact select_avx2_spec 8#usize 2 (by decide) (Or.inl rfl) z table index token hrows
  | none => exact select_sse2_spec 8#usize 4 (by decide) rfl z table index hrows

/-- `bignum_aff_point_select_p384` returns row `index` of P-384's table of
12-word affine points, or zeros. -/
@[step]
theorem bignum_aff_point_select_p384_spec (hc : RunsSelect) (z : Std.Array U64 12#usize)
    (table : Slice U64) (index : U8) (hrows : table.length / 12 < 2 ^ 32) :
    low.x86_64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
      r.val = tableRow 12 table.val index.val ⦄ := by
  obtain ⟨t, ht⟩ := hc
  unfold low.x86_64.bignum_point_select.bignum_aff_point_select_p384
  simp only [ht, bind_ok, bind_tc_ok]
  cases t with
  | some token => exact select_avx2_spec 12#usize 3 (by decide) (Or.inl rfl) z table index token hrows
  | none => exact select_sse2_spec 12#usize 6 (by decide) rfl z table index hrows

/-- `bignum_aff_point_select_p521` returns row `index` of P-521's table of
18-word affine points, or zeros. -/
@[step]
theorem bignum_aff_point_select_p521_spec (hc : RunsSelect) (z : Std.Array U64 18#usize)
    (table : Slice U64) (index : U8) (hrows : table.length / 18 < 2 ^ 32) :
    low.x86_64.bignum_point_select.bignum_aff_point_select_p521 z table index ⦃ r =>
      r.val = tableRow 18 table.val index.val ⦄ := by
  obtain ⟨t, ht⟩ := hc
  unfold low.x86_64.bignum_point_select.bignum_aff_point_select_p521
  simp only [ht, bind_ok, bind_tc_ok]
  cases t with
  | some token => exact select_avx2_spec 18#usize 4 (by decide) (Or.inr rfl) z table index token hrows
  | none => exact select_sse2_spec 18#usize 9 (by decide) rfl z table index hrows

/-- `bignum_aff_point_select_p384` on a 16-row table, in the form P-384's
key generation takes it. -/
theorem bignum_aff_point_select_p384_rows16 (hc : RunsSelect) :
    ∀ (z : Std.Array U64 12#usize) (table : Slice U64) (index : U8), table.length = 192 →
      low.x86_64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
        r.val = if 1 ≤ index.val ∧ index.val ≤ 16 then (table.val.drop (12 * (index.val - 1))).take 12
          else List.replicate 12 0#u64 ⦄ := by
  intro z table index h
  have h' : table.val.length = 192 := h
  have := bignum_aff_point_select_p384_spec hc z table index (by rw [h]; decide)
  simp only [tableRow, h'] at this
  exact this

end rind.x86_64
