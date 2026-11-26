module

public import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Co-Z doubling and addition on numbered slots

DBLU and ZADDU (Goundar, Joye, Miyaji, Rivain and Venelli, "Scalar
multiplication on Weierstraß elliptic curves from Co-Z arithmetic"), for
`a = -3`, on the slots `0, 1, …` of a field program:

* `dblu`, from an affine `P = (13, 14)`, with `15` the field's one: `2P` at
  `(8, 9, 10)`, and `P` at the same `Z` at `(5, 4)`;
* `zaddu`, of `D = (0, 1)` and `T = (8, 9)` sharing the `Z` at `10`: `T + D`
  at `(8, 9, 10)`, and `D` at its new `Z` at `(0, 1)`.

The slots `2 … 7` are temporaries. These are the operations of ECDH's table
(`Proof/P256/EcdhJac/Dblu.lean`) without its last two, which keep the
square and cube of `Z`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.CoZ

/-- An operation on the slots `σ` names. -/
def rename (σ : Nat → Nat) : FOp → FOp
  | .mul o a b => .mul (σ o) (σ a) (σ b)
  | .add o a b => .add (σ o) (σ a) (σ b)
  | .sub o a b => .sub (σ o) (σ a) (σ b)

def dblu : List FOp :=
  [.mul 2 13 13, .mul 3 14 14, .mul 4 3 3, .mul 5 13 3, .add 5 5 5, .add 5 5 5, .sub 6 2 15,
   .add 7 6 6, .add 6 7 6, .mul 8 6 6, .sub 8 8 5, .sub 8 8 5, .sub 7 5 8, .mul 9 6 7,
   .add 4 4 4, .add 4 4 4, .add 4 4 4, .sub 9 9 4, .add 10 14 14]

def zaddu : List FOp :=
  [.sub 2 0 8, .mul 3 2 2, .mul 10 10 2, .mul 0 0 3, .mul 5 8 3, .sub 6 1 9, .mul 7 6 6,
   .sub 4 0 5, .mul 1 1 4, .sub 8 7 0, .sub 8 8 5, .sub 9 0 8, .mul 9 6 9, .sub 9 9 1]

end VG.Impl.Weierstrass.CoZ
