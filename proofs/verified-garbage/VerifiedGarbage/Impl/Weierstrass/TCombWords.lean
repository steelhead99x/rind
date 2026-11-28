module

/-!
# The fixed-base comb's tables as words, on any target

The words of a comb's tables of constants (`Artifact.consts`), as every
target's comb reads them (`Impl/Weierstrass/<Target>/TComb.lean`): table
after table, entry after entry, `x` then `y`, each in Montgomery form, `n`
64-bit words little-endian (`tcombWords`).
-/

@[expose] public section

namespace VG.Impl.Weierstrass

/-- Word `w` of `v`. -/
def wordOf (v w : Nat) : BitVec 64 := BitVec.ofNat 64 (v >>> (64 * w))

/-- The words of the tables `tbl` (affine points, below `p`) in Montgomery form
(`R`), `n` words a coordinate, little-endian: table after table, entry after
entry, `x` then `y`. -/
def tcombWords (n R p : Nat) (tbl : List (List (Nat × Nat))) : List (BitVec 64) :=
  tbl.flatMap fun t => t.flatMap fun (x, y) =>
    (List.range n).map (wordOf (x * R % p)) ++ (List.range n).map (wordOf (y * R % p))

end VG.Impl.Weierstrass
