import Rind.X86_64.S2nBignum
import Rind.X86_64.PointSelect
open Aeneas Aeneas.Std Result

/-!
# P-384's comb select, where rind runs

What `Rind.X86_64.P384Keygen`, which `admin/prove` also writes for aarch64,
needs of `bignum_aff_point_select_p384`: row `index` of a 16-row table, or
zeros. `Rind.X86_64.PointSelect` proves it for whichever select
`HaveAvx2::check` picks, which `Runs` says returns; aarch64's own
`P384Select.lean` states it from `Rind.Aarch64.PointSelect`.
-/

namespace rind.x86_64

theorem p384_aff_select (h : Runs) :
    ∀ (z : Std.Array U64 12#usize) (table : Slice U64) (index : U8), table.length = 192 →
      low.x86_64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
        r.val = if 1 ≤ index.val ∧ index.val ≤ 16 then (table.val.drop (12 * (index.val - 1))).take 12
          else List.replicate 12 0#u64 ⦄ :=
  bignum_aff_point_select_p384_rows16 h.2.2.2

end rind.x86_64
