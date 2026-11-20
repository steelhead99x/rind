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

/-- FIPS 186-5 section 6.4.1's P-384 ECDSA signature. -/
noncomputable abbrev ecdsaP384Sign : Nat → Nat → Nat → Option (Nat × Nat) := nist.ecdsaSign p384 n384 p384G

/-- FIPS 186-5 section 6.4.2's P-384 ECDSA verification under the public key
`Q`. -/
abbrev ecdsaP384Verifies : nist.Point → Nat → Nat → Nat → Prop := nist.ecdsaVerifies p384 n384 p384G

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
https://github.com/awslabs/s2n-bignum/blob/3f01260ff1bd2577abf0117ce45aa008bc243a80/arm/proofs/p384_montjmixadd_alt.ml#L3736 -/
def p384Represents2 (P : nist.Point) (xy : Nat × Nat) : Prop :=
  xy.1 < p384 ∧ xy.2 < p384 ∧ some (p384RInv * xy.1 % p384, p384RInv * xy.2 % p384) = P

/-- `represents_p384 P (x, y, z)`: each coordinate is below p, and the
Jacobian point their Montgomery forms decode to (`montgomery_decode`) is `P`,
https://github.com/awslabs/s2n-bignum/blob/3f01260ff1bd2577abf0117ce45aa008bc243a80/arm/proofs/p384_montjadd_alt.ml#L5051 -/
def p384Represents (P : nist.Point) (xyz : Nat × Nat × Nat) : Prop :=
  xyz.1 < p384 ∧ xyz.2.1 < p384 ∧ xyz.2.2 < p384 ∧
    nist.ofJacobian p384 (p384RInv * xyz.1 % p384) (p384RInv * xyz.2.1 % p384)
      (p384RInv * xyz.2.2 % p384) = P

/-! ## P-521 -/

/-- `p_521`, the field's prime, 2⁵²¹ - 1, from HOL Light's `EC/nistp521.ml` at
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp521.ml -/
def p521 : Nat :=
  6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151

/-- `n_521`, the group's order. -/
def n521 : Nat :=
  6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449

/-- `b_521`, the curve's constant term; its `a` is -3. -/
def b521 : Nat :=
  0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00

/-- `G_521`, the generator. -/
def p521G : nist.Point :=
  some (0x00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66,
    0x011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650)

/-- Whether a point is in `group_carrier p521_group`, by `P521_GROUP`. -/
abbrev p521OnCurve : nist.Point → Prop := nist.OnCurve p521 b521

/-- `group_mul p521_group`, by `P521_GROUP`. -/
noncomputable abbrev p521Add : nist.Point → nist.Point → nist.Point := nist.add p521

/-- `group_pow p521_group`. -/
noncomputable abbrev p521Pow : nist.Point → Nat → nist.Point := nist.pow p521

/-- `group_inv p521_group`, by `P521_GROUP`. -/
abbrev p521Neg : nist.Point → nist.Point := nist.neg p521

/-- FIPS 186-5 section 6.4.1's P-521 ECDSA signature. -/
noncomputable abbrev ecdsaP521Sign : Nat → Nat → Nat → Option (Nat × Nat) := nist.ecdsaSign p521 n521 p521G

/-- FIPS 186-5 section 6.4.2's P-521 ECDSA verification under the public key
`Q`. -/
abbrev ecdsaP521Verifies : nist.Point → Nat → Nat → Nat → Prop := nist.ecdsaVerifies p521 n521 p521G

end rind.spec
