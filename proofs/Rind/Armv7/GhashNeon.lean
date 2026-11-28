import Rind.Armv7.AesGcm
import Rind.S2nGcm
open Aeneas Aeneas.Std Result rind.vale rind.s2n Polynomial

/-!
# GHASH on armv7's NEON

`low::arm::ghash_armv4`'s `NeonTable` runs aws-lc's `gcm_init_neon` and
`gcm_ghash_neon`, which `proofs/hol-light/armv7/gcm_init_neon.ml` and
`gcm_ghash_neon.ml` prove, on s2n-bignum's AArch32 model of the bytes rind's
build emits, compute SP 800-38D's GHASH: the first stores the key twisted, as
s2n-bignum's `ghash_twist` does, and the second folds whole blocks into the
state as `nist_ghash` does under the key whose twist the table holds. Each
axiom here restates one of those theorems, at rind's commit, about the opaque
Rust wrapper around the routine, over `Rind.S2nGcm`'s transliterations of
`ghash_twist` and `nist_ghash`, and `neon_new_ghashFor` composes them: the
table `NeonTable::new` builds hashes as `GhashFor` asks.

Trusted: each restatement, and that each call meets its theorem's premises,
which every call safe Rust makes does: the table is 16-byte aligned
(`repr(align(16))`), no Rust object wraps the address space or overlaps the
code, `ghash` skips the routine for no blocks, and a slice on armv7 spans
fewer than 2^31 bytes, so `16 * n < 2 ^ 32`. Neither routine's constant time
is proven.
-/

local notation "P" => Polynomial (ZMod 2)

namespace rind.armv7

open low.arm.ghash_armv4 (NeonTable)

/-- The table's 16 bytes as the routines read them: their little-endian
value, `bytes128` at its address. -/
opaque neonTableValue : NeonTable → BitVec 128

/-- `GCM_INIT_NEON_SUBROUTINE_CORRECT`: `new` passes `h` as two words, the
big-endian values of its first and last eight bytes, whose join is
`blockBE h`, and the routine stores that key's twist. -/
@[step]
axiom neon_table_new_spec (h : Std.Array U8 16#usize) (token : low.arm.cpu.HaveNeon) :
    NeonTable.new h token ⦃ t => neonTableValue t = ghashTwist (blockBE h.val) ⦄

/-- `GCM_GHASH_NEON_SUBROUTINE_CORRECT`: the routine reads `xi` and each block
as little-endian values, whose byte reversals are their `blockBE`s, and
folds the blocks into `xi` as `nist_ghash` does under the key `h` whose twist
the table holds. With no blocks, `ghash` returns `xi` without calling the
routine, which reads a block before checking the length, and `nist_ghash`
returns it too. -/
@[step]
axiom neon_table_ghash_spec (t : NeonTable) (h : BitVec 128) (ht : neonTableValue t = ghashTwist h)
    (xi : Std.Array U8 16#usize) (input : Slice (Std.Array U8 16#usize)) :
    NeonTable.ghash t xi input ⦃ r =>
      blockBE r.val = nistGhash h (blockBE xi.val) (input.val.map fun b => blockBE b.val) ⦄

/-- A table holding the twist of `h` hashes as GHASH does under `h`. -/
theorem neon_ghashFor (h : BitVec 128) (t : NeonTable) (ht : neonTableValue t = ghashTwist h) :
    GhashFor (toPoly h) NeonTable.Insts.RindMidAes_gcmGhash t := fun xi input => by
  apply WP.spec_mono (neon_table_ghash_spec t h ht xi input)
  intro r hr
  rw [hr, toPoly_nistGhash, List.map_map, Function.comp_def]

/-- `NeonTable::new` builds a table that hashes as GHASH does under `h`. -/
theorem neon_new_ghashFor (h : Std.Array U8 16#usize) (token : low.arm.cpu.HaveNeon) :
    NeonTable.new h token ⦃ t => GhashFor (toPoly (blockBE h.val)) NeonTable.Insts.RindMidAes_gcmGhash t ⦄ :=
  WP.spec_mono (neon_table_new_spec h token) fun t ht => neon_ghashFor _ t ht

end rind.armv7
