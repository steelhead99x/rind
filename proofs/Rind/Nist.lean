import Rind.Spec

/-!
# P-384

P-384's parameters on `Rind.Spec`'s group law of the NIST curves, from HOL
Light's `EC/nistp384.ml` at
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp384.ml
-/

namespace rind.spec

/-! ## P-384 -/

/-- `p_384`, the field's prime. -/
def p384 : Nat :=
  39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- `n_384`, the group's order. -/
def n384 : Nat :=
  39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

/-- `b_384`, the curve's constant term; its `a` is -3. -/
def b384 : Nat :=
  0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef

/-- `G_384`, the generator. -/
def p384G : nist.Point :=
  some (0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7,
    0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f)

/-- Whether a point is in `group_carrier p384_group`, by `P384_GROUP`. -/
abbrev p384OnCurve : nist.Point → Prop := nist.OnCurve p384 b384

/-- `group_mul p384_group`, by `P384_GROUP`. -/
noncomputable abbrev p384Add : nist.Point → nist.Point → nist.Point := nist.add p384

/-- `group_pow p384_group`. -/
noncomputable abbrev p384Pow : nist.Point → Nat → nist.Point := nist.pow p384

/-- `group_inv p384_group`, by `P384_GROUP`. -/
abbrev p384Neg : nist.Point → nist.Point := nist.neg p384

/-! ### s2n-bignum's representations of P-384's points -/

/-- HOL Light's `inverse_mod p_384 (2 EXP 384)`: the number below `p384`
that 2³⁸⁴ times is 1 mod `p384`, which `p384RInv_spec` checks, and which is
unique since `p384` is odd. -/
def p384RInv : Nat :=
  183479889321925461653251752109332205360611897149516305954304919627392402791260477631193651879713439593005062

set_option exponentiation.threshold 384 in
theorem p384RInv_spec : p384RInv < p384 ∧ 2 ^ 384 * p384RInv % p384 = 1 := by
  simp only [p384RInv, p384]; decide

/-- The three coordinates at `xyz` as HOL Light's
`bignum_triple_from_memory (xyz,6)` reads them. -/
def tripleNat6 (xyz : List Aeneas.Std.U64) : Nat × Nat × Nat :=
  (wordsNat (xyz.take 6), wordsNat ((xyz.drop 6).take 6), wordsNat ((xyz.drop 12).take 6))

/-- The two coordinates at `xy` as HOL Light's
`bignum_pair_from_memory (xy,6)` reads them. -/
def pairNat6 (xy : List Aeneas.Std.U64) : Nat × Nat :=
  (wordsNat (xy.take 6), wordsNat ((xy.drop 6).take 6))

/-- `weierstrass_of_jacobian (integer_mod_ring p) (x, y, z)`: infinity for
z of zero, and otherwise (x / z², y / z³) in the field of integers mod p, whose
inverses `ZMod`'s are,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/jacobian.ml#L21 -/
def nist.ofJacobian (p x y z : Nat) : nist.Point :=
  if z = 0 then none
  else some (((x : ZMod p) * ((z : ZMod p) ^ 2)⁻¹).val, ((y : ZMod p) * ((z : ZMod p) ^ 3)⁻¹).val)

/-- `represents2_p384 P (x, y)`: `P` is the finite point whose coordinates
in Montgomery form (`montgomery_decode`) are `x` and `y`, each below `p384`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p384_montjmixadd_alt.ml#L3736 -/
def p384Represents2 (P : nist.Point) (xy : Nat × Nat) : Prop :=
  xy.1 < p384 ∧ xy.2 < p384 ∧ some (p384RInv * xy.1 % p384, p384RInv * xy.2 % p384) = P

/-- `represents_p384 P (x, y, z)`: each coordinate is below p, and the
Jacobian point their Montgomery forms decode to (`montgomery_decode`) is `P`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p384_montjadd_alt.ml#L5051 -/
def p384Represents (P : nist.Point) (xyz : Nat × Nat × Nat) : Prop :=
  xyz.1 < p384 ∧ xyz.2.1 < p384 ∧ xyz.2.2 < p384 ∧
    nist.ofJacobian p384 (p384RInv * xyz.1 % p384) (p384RInv * xyz.2.1 % p384)
      (p384RInv * xyz.2.2 % p384) = P

end rind.spec
