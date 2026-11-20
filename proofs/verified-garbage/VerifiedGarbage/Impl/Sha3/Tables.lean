module

/-!
# Keccak-f[1600]: tables shared by the implementations

ρ's rotations, π's lane permutation and the lanes kept complemented, as
tables, for every target's implementation. (`Proof/Sha3/Spec.lean` proves
the first two against the specification; `Proof/Sha3/Compl.lean` uses the
third.)
-/

@[expose] public section

namespace VG.Impl.Sha3

/-- The rotation (left) of lane `i` by ρ (Algorithm 2), as a table. -/
def rhoOff (i : Nat) : Nat :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8,
    18, 2, 61, 56, 14].getD i 0

/-- The lane of `A` that π moves to `(x, y)`: `((x + 3y) mod 5, x)`. -/
def piSrc (x y : Nat) : Nat := (x + 3 * y) % 5 + 5 * x

/-- The lanes that implementations using the "lane complementing" transform
(the Keccak team's implementation overview, §2.2) keep complemented between
rounds: with them, χ needs one NOT per plane. -/
def complLanes : List Nat := [1, 2, 8, 12, 17, 20]

end VG.Impl.Sha3
