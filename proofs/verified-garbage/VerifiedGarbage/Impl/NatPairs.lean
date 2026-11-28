module

public meta import Lean.Elab.ElabRules

/-!
# Tables of pairs of numerals

Untrusted: this only builds terms, which the kernel checks as usual.

`nat_pairs% [(a₀, b₀), (a₁, b₁), …]` is the list `[(a₀, b₀), (a₁, b₁), …] :
List (Nat × Nat)`, built directly as the term the elaborator builds for it
(each numeral `@OfNat.ofNat Nat n (instOfNatNat n)`). The comb tables
(`Impl/<Curve>/CombTable7.lean`) have thousands of numerals, which the term
elaborator took most of their modules' time over, a numeral and a pair at a
time.
-/

public meta section

namespace VG.Impl.NatPairs
open Lean Elab

/-- `@OfNat.ofNat Nat n (instOfNatNat n)`, the numeral `n : Nat`. -/
def natLit (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

/-- The list of the pairs, as `List (Nat × Nat)`. -/
def pairs (ps : Array (Nat × Nat)) : Expr := Id.run do
  let nat := mkConst ``Nat
  let pt := mkApp2 (mkConst ``Prod [.zero, .zero]) nat nat
  let mut e := mkApp (mkConst ``List.nil [.zero]) pt
  for (a, b) in ps.reverse do
    e := mkApp3 (mkConst ``List.cons [.zero]) pt
      (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) nat nat (natLit a) (natLit b)) e
  return e

end VG.Impl.NatPairs

/-- `nat_pairs% [(a, b), …]`: the list of pairs of numerals, `List (Nat × Nat)`. -/
syntax (name := natPairs) "nat_pairs% " "[" ("(" num ", " num ")"),* "]" : term

open Lean Elab in
elab_rules : term
  | `(nat_pairs% [$[($as, $bs)],*]) =>
    return VG.Impl.NatPairs.pairs ((as.zip bs).map fun (a, b) => (a.getNat, b.getNat))
