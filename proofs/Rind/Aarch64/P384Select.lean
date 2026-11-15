import Rind.Aarch64.S2nBignum
import Rind.Aarch64.PointSelect
open Aeneas Aeneas.Std Result

/-!
# P-384's comb select, where rind runs

What `Rind.Aarch64.P384Keygen`, which `admin/prove` writes from x86_64's,
needs of `bignum_aff_point_select_p384`: row `index` of a 16-row table, or
zeros, which `Rind.Aarch64.PointSelect` proves of the NEON select every
aarch64 CPU rind runs on takes. It takes `Runs` only to match x86_64's
`P384Select.lean`, whose select dispatches on the CPU.
-/

namespace rind.aarch64

theorem p384_aff_select (_ : Runs) :
    ∀ (z : Std.Array U64 12#usize) (table : Slice U64) (index : U8), table.length = 192 →
      low.aarch64.bignum_point_select.bignum_aff_point_select_p384 z table index ⦃ r =>
        r.val = if 1 ≤ index.val ∧ index.val ≤ 16 then (table.val.drop (12 * (index.val - 1))).take 12
          else List.replicate 12 0#u64 ⦄ :=
  bignum_aff_point_select_p384_rows16

end rind.aarch64
