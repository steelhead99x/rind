module
public import Rind.Aarch64.FunsExternal
public import Rind.RowSelect
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false

/-!
# aarch64's point select, proven

`select_spec` proves that `Rind.Aarch64.PointSelectModel`'s model of
`select::<N, V>` returns row `index` of a table of `N`-word rows, counting
from 1, or zeros for an index of 0 or past the last row, for every `N` its
`const` assertion admits and every table of fewer than 2^32 rows, whose 32-bit
counters do not wrap. So `bignum_aff_point_select_p384` selects that row.
-/

namespace rind.aarch64

open rind.simd rind.select

theorem vceqq_bcast (a b : BitVec 32) :
    core.core_arch.arm_shared.neon.generated.vceqq_u32 (ofLanes32 fun _ => a) (ofLanes32 fun _ => b) =
      ok (if a = b then BitVec.allOnes 128 else 0) := by
  unfold core.core_arch.arm_shared.neon.generated.vceqq_u32; rw [cmpeq128_bcast]

theorem vaddq_bcast (a b : BitVec 32) :
    core.core_arch.arm_shared.neon.generated.vaddq_u32 (ofLanes32 fun _ => a) (ofLanes32 fun _ => b) =
      ok (ofLanes32 fun _ => a + b) := by
  unfold core.core_arch.arm_shared.neon.generated.vaddq_u32; rw [add128_bcast]

section
variable (N : Nat) (table : List U64) (index : U8)

/-- `_select`'s state after `k` rows. -/
def selectAfter (V k : Nat) : BitVec 128 × List (BitVec 128) :=
  (ofLanes32 fun _ => 1#32 + BitVec.ofNat 32 k,
    (List.range V).map fun i => if picked index k then load128 (row N table (index.val - 1)) (2 * i) else 0)

theorem row_step (V k : Nat) (hk : k + 1 < 2 ^ 32) :
    low.aarch64.bignum_point_select.select_row V
      (ofLanes32 fun _ => index.bv.setWidth 32) (ofLanes32 fun _ => 1#32)
      (selectAfter N table index V k) (row N table k) = ok (selectAfter N table index V (k + 1)) := by
  simp only [low.aarch64.bignum_point_select.select_row, selectAfter, vceqq_bcast, vaddq_bcast,
    core.core_arch.arm_shared.neon.generated.vandq_u32, core.core_arch.arm_shared.neon.generated.veorq_u32,
    bind_ok, mapM_ok, and_mask, counter_eq k index hk, counter_succ]
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

theorem select_loop (V : Nat) : ∀ k, k < 2 ^ 32 →
    (List.range k).foldlM (fun st r => low.aarch64.bignum_point_select.select_row V
      (ofLanes32 fun _ => index.bv.setWidth 32) (ofLanes32 fun _ => 1#32) st (row N table r))
      (selectAfter N table index V 0) = ok (selectAfter N table index V k)
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [List.range_succ, List.foldlM_append, select_loop V k (by omega), bind_tc_ok,
      List.foldlM_cons, row_step N table index V k hk, List.foldlM_nil, pure_tc_eq]

theorem selectAfter_zero (V : Nat) :
    selectAfter N table index V 0 = ((ofLanes32 fun _ => 1#32), List.replicate V 0) := by
  have h1 : 1#32 + BitVec.ofNat 32 0 = 1#32 := by decide
  simp only [selectAfter, picked_zero, h1, ite_false, List.map_const', List.length_range]

end

theorem u32_mk_bv (x : BitVec 32) : (⟨x⟩ : Std.U32).bv = x := rfl

theorem one_u32_bv : (1#u32 : Std.U32).bv = 1#32 := rfl

theorem select_spec (N : Std.Usize) (V : Nat) (h0 : 0 < N.val) (hN : N.val = 2 * V)
    (z : Std.Array U64 N) (table : Slice U64) (index : U8)
    (hrows : table.length / N.val < 2 ^ 32) :
    low.aarch64.bignum_point_select.select N V z table index ⦃ r =>
      r.val = tableRow N.val table.val index.val ⦄ := by
  unfold low.aarch64.bignum_point_select.select
  rw [ite_eq_left ⟨h0, hN⟩]
  have hrows' : table.val.length / N.val < 2 ^ 32 := hrows
  have hloop := select_loop N.val table.val index V _ hrows'
  rw [selectAfter_zero] at hloop
  simp only [core.core_arch.arm_shared.neon.generated.vdupq_n_u32, bind_ok, bind_tc_ok,
    List.foldlM_map, u32_mk_bv, one_u32_bv]
  rw [hloop]
  simp only [bind_ok, bind_tc_ok, selectAfter]
  rw [tableRow_eq]
  by_cases hp : picked index (table.val.length / N.val)
  · have hlen := row_length N.val table.val (r := index.val - 1) (by unfold picked at hp; omega)
    simp only [hp, ite_true]
    have hlen2 : (row N.val table.val (index.val - 1)).length = 2 * V := by rw [hlen, hN]
    simp only [out128 _ V hlen2]
    rw [dite_eq_left hlen, WP.spec_ok, Array.from_val]
  · simp only [hp, ite_false, out128_zero V, ← hN]
    rw [dite_eq_left (List.length_replicate ..), WP.spec_ok, Array.from_val]

/-- `bignum_aff_point_select_p384` returns row `index` of P-384's table of
12-word affine points, or zeros. -/
@[step]
theorem bignum_aff_point_select_p384_spec (z : Std.Array U64 12#usize)
    (table : Slice U64) (index : U8) (hrows : table.length / 12 < 2 ^ 32) :
    low.aarch64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
      r.val = tableRow 12 table.val index.val ⦄ :=
  select_spec 12#usize 6 (by decide) rfl z table index hrows

/-- `bignum_aff_point_select_p384` on a 16-row table, in the form P-384's
key generation takes it. -/
theorem bignum_aff_point_select_p384_rows16 :
    ∀ (z : Std.Array U64 12#usize) (table : Slice U64) (index : U8), table.length = 192 →
      low.aarch64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
        r.val = if 1 ≤ index.val ∧ index.val ≤ 16 then (table.val.drop (12 * (index.val - 1))).take 12
          else List.replicate 12 0#u64 ⦄ := by
  intro z table index h
  have h' : table.val.length = 192 := h
  have := bignum_aff_point_select_p384_spec z table index (by rw [h]; decide)
  simp only [tableRow, h'] at this
  exact this

end rind.aarch64
