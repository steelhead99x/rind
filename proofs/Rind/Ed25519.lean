module
public import Rind.Spec
public import Rind.Sha2
@[expose] public section
open Aeneas Aeneas.Std

/-!
# What rind's Ed25519 computes

RFC 8032's PureEd25519 over HOL Light's `edwards25519_group`, defined in
`EC/edwards25519.ml` at
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/edwards25519.ml,
with s2n-bignum's encoding of its points, the definitions s2n-bignum's
theorems state their routines' results in. The group's multiplication and
power stay opaque: nothing is assumed of them beyond the routine contracts in
`Rind.<Arch>.S2nBignum`.
-/

namespace rind.spec

/-- `p_25519`, the field's prime. -/
def p25519 : Nat := 2 ^ 255 - 19

/-- `n_25519`, the base point's order, which RFC 8032 calls L. -/
def n25519 : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- `e_25519`, the curve's `a`, which is -1. -/
def e25519 : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819948

/-- `d_25519`, the curve's `d`. -/
def d25519 : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- A point of `edwards25519_group` as HOL Light writes one: a pair of
integers, which the group's carrier keeps in `integer_mod_ring p_25519`. -/
abbrev EdPoint := Int × Int

/-- Whether a point is in `group_carrier edwards25519_group`, which
`EDWARDS25519_GROUP` shows is `edwards_curve (integer_mod_ring p_25519,
&e_25519, &d_25519)`: coordinates in [0, p) that satisfy
e·x² + y² = 1 + d·x²·y², with `integer_mod_ring`'s arithmetic mod p,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/edwards25519.ml#L92

The proofs must decide this membership, so the composition rule lets it be
this defining equation rather than an opaque set. -/
def edOnCurve (P : EdPoint) : Prop :=
  0 ≤ P.1 ∧ P.1 < p25519 ∧ 0 ≤ P.2 ∧ P.2 < p25519 ∧
    (e25519 * P.1 ^ 2 + P.2 ^ 2) % (p25519 : Int) = (1 + d25519 * P.1 ^ 2 * P.2 ^ 2) % (p25519 : Int)

/-- `E_25519`, the base point, which RFC 8032 calls B. -/
def edB : EdPoint :=
  (0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a,
    0x6666666666666666666666666666666666666666666666666666666666666658)

/-- `group_pow edwards25519_group P n`, the point `P` multiplied by `n`.

It is opaque here: nothing is assumed of it beyond the routine contracts in
`Rind.<Arch>.S2nBignum`, which restate s2n-bignum's theorems about it. -/
opaque edPow : EdPoint → Nat → EdPoint

/-- `group_mul edwards25519_group P Q`, the sum of two points.

It is opaque here: nothing is assumed of it beyond the routine contracts in
`Rind.<Arch>.S2nBignum`, which restate s2n-bignum's theorems about it. -/
opaque edMul : EdPoint → EdPoint → EdPoint

/-- `edwards_neg (integer_mod_ring p_25519, &e_25519, &d_25519) P`, which
`EDWARDS25519_GROUP` shows is `group_inv edwards25519_group P`: x negated mod
p. -/
def edNeg (P : EdPoint) : EdPoint := ((-P.1) % (p25519 : Int), P.2)

/-- `modular_encode (256, p_25519)`: the number below p an integer is
congruent to. -/
def edModEncode (x : Int) : Nat := (x % (p25519 : Int)).toNat

/-- `paired (modular_encode (256, p_25519)) P`: a point's coordinates as
numbers below p, as s2n-bignum's routines write them. -/
def edModEncodePair (P : EdPoint) : Nat × Nat := (edModEncode P.1, edModEncode P.2)

/-- `paired (modular_decode (256, p_25519)) xy`: the point whose coordinates
are `xy`'s, reduced mod p. -/
def edModDecodePair (xy : Nat × Nat) : EdPoint :=
  ((xy.1 : Int) % (p25519 : Int), (xy.2 : Int) % (p25519 : Int))

/-- s2n-bignum's `ed25519_encode`, RFC 8032 5.1.2's encoding of a point as a
number: its y-coordinate, with the low bit of its x-coordinate as bit 255,
https://github.com/awslabs/s2n-bignum/blob/3f01260ff1bd2577abf0117ce45aa008bc243a80/x86/proofs/edwards25519_decode.ml#L1350 -/
def edEncode (P : EdPoint) : Nat := 2 ^ 255 * (edModEncode P.1 % 2) + edModEncode P.2

/-- s2n-bignum's `ed25519_validencode n`: some point of the group encodes as
`n`. -/
def edValidEncode (n : Nat) : Prop := ∃ P, edOnCurve P ∧ edEncode P = n

/-- s2n-bignum's `ed25519_decode n`, a point of the group that encodes as `n`,
picked by Hilbert's choice as HOL Light's `@` picks it,
https://github.com/awslabs/s2n-bignum/blob/3f01260ff1bd2577abf0117ce45aa008bc243a80/x86/proofs/edwards25519_decode.ml#L1361 -/
noncomputable def edDecode (n : Nat) : EdPoint :=
  Classical.epsilon fun P => edOnCurve P ∧ edEncode P = n

/-- The `y` of each point of small order whose encoding fits in 255 bits, as
libsodium's `ge25519_has_small_order` lists them: those of the eight points of
order dividing 8, then p and p + 1, the non-canonical forms of 0 and 1. -/
def edSmallOrderY : List Nat :=
  [0, 1, 2707385501144840649318225287225658788936804267575313519463743609750303402022,
    55188659117513257062467267217118295137698188065244968500265048394206261417927,
    p25519 - 1, p25519, p25519 + 1]

/-- The `k` little-endian bytes of `n` mod 256ᵏ. -/
def leBytesOf (k n : Nat) : List U8 :=
  (List.range k).map fun i => @UScalar.mk UScalarTy.U8 (BitVec.ofNat 8 (n / 256 ^ i))

/-- RFC 8032 5.1.5's pruning of a secret scalar `a`, read from 32 bytes: its
lowest three bits and bit 255 cleared, and bit 254 set. -/
def edClamp (a : Nat) : Nat := 2 ^ 254 + a % 2 ^ 254 / 8 * 8

/-- RFC 8032 5.1.5's secret scalar of a private key, its 32-byte seed. -/
def ed25519Scalar (seed : List U8) : Nat := edClamp (leNat ((sha512 seed).take 32))

/-- RFC 8032 5.1.5's public key of a private key: the encoding of the base
point times its secret scalar. -/
def ed25519PublicKey (seed : List U8) : List U8 :=
  leBytesOf 32 (edEncode (edPow edB (ed25519Scalar seed)))

/-- RFC 8032 5.1.6's PureEd25519 signature of `msg` under a private key, its
32-byte seed: the encoding of R = rB, for r the hash of the seed's hash's
second half and the message, then S = r + ks mod L, for k the hash of R, the
public key, and the message. -/
def ed25519Sign (seed msg : List U8) : List U8 :=
  let r := leNat (sha512 ((sha512 seed).drop 32 ++ msg)) % n25519
  let R := leBytesOf 32 (edEncode (edPow edB r))
  let k := leNat (sha512 (R ++ ed25519PublicKey seed ++ msg)) % n25519
  R ++ leBytesOf 32 ((k * ed25519Scalar seed + r) % n25519)

/-- RFC 8032 5.1.7's verification of `sig` over `msg`, for the public key
whose bytes are `key` and whose point is `A`: `sig` is 64 bytes, its S is
below L, and its R encodes SB - kA, for k the hash of R, the key, and the
message. rind compares encodings, as RFC 8032's cofactorless check allows. -/
def ed25519Verifies (A : EdPoint) (key msg sig : List U8) : Prop :=
  sig.length = 64 ∧ leNat (sig.drop 32) < n25519 ∧
    leNat (sig.take 32) =
      edEncode (edMul (edPow (edNeg A) (leNat (sha512 (sig.take 32 ++ key ++ msg)) % n25519))
        (edPow edB (leNat (sig.drop 32))))

end rind.spec
