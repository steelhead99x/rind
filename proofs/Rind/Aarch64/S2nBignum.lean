import Rind.Aarch64.Funs
import Rind.Spec
import Rind.Ed25519
import Rind.Keccak
import Rind.Nist
open Aeneas Aeneas.Std Result rind.spec

/-!
# s2n-bignum's contracts on aarch64

Each axiom restates one of s2n-bignum's HOL Light theorems, at the revision
rind transliterates (b4f17ee7), about the opaque Rust wrapper
`admin/parse-asm` generates around that routine. rind's aarch64 X25519 runs
the `_alt` sources under the plain names, and so does its Ed25519 for the
scalar multiplications, decoding, and `bignum_madd_n25519`, and its P-384 for
field multiplication and squaring and the point routines. The theorem's
preconditions hold for every call from safe Rust: the `&mut` result cannot overlap an input or
the routine's code or table, the routine's stack lies below the caller's
frame, and the ABI keeps the stack pointer 16-byte aligned. Its total correctness
(`ensures`) gives the `ok`.

The restatement, and that rind's inline assembly is s2n-bignum's object code
and constant table with the wrapper passing the arguments the theorem names,
are trusted. `bignum_eq`'s theorem is instead rind's own, of the bytes rind's
build emits, so only the wrapper's arguments are trusted there.
-/

namespace rind.aarch64

/-- `CURVE25519_X25519_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/curve25519_x25519_alt.ml#L5349 -/
@[step]
axiom curve25519_x25519_spec (res scalar point : Std.Array U64 4#usize) :
    low.aarch64.curve25519_x25519.curve25519_x25519 res scalar point ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) (wordsNat point.val) ⦄

/-- `CURVE25519_X25519BASE_ALT_SUBROUTINE_CORRECT`, whose `tables`
precondition holds because rind's copy of the constant table is s2n-bignum's,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/curve25519_x25519base_alt.ml#L3700 -/
@[step]
axiom curve25519_x25519base_spec (res scalar : Std.Array U64 4#usize) :
    low.aarch64.curve25519_x25519base.curve25519_x25519base res scalar ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) 9 ⦄

/-- `BIGNUM_EQ_CORRECT`, rind's own proof of the wrapper's `asm!` block, as
rind's build emits it, which ends where the block does, and whose 1 or 0 the
wrapper returns as `true` or `false`, in `proofs/hol-light/aarch64/bignum_eq.ml`
at rind's commit. -/
@[step]
axiom bignum_eq_spec (x y : Slice U64) :
    low.aarch64.bignum_eq.bignum_eq x y ⦃ b => b = decide (wordsNat x.val = wordsNat y.val) ⦄

/-! ### Ed25519 -/

/-- `EDWARDS25519_DECODE_ALT_SUBROUTINE_CORRECT`, whose 0 for a valid
encoding the wrapper returns as `true`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/edwards25519_decode_alt.ml#L1703 -/
@[step]
axiom edwards25519_decode_spec (z : Std.Array U64 8#usize) (c : Std.Array U8 32#usize) :
    low.aarch64.edwards25519_decode.edwards25519_decode z c ⦃ r =>
      (r.1 = true ↔ edValidEncode (leNat c.val)) ∧
        (edValidEncode (leNat c.val) → pairNat r.2.val = edModEncodePair (edDecode (leNat c.val))) ⦄

/-- `EDWARDS25519_SCALARMULBASE_ALT_SUBROUTINE_CORRECT`, whose `tables`
preconditions hold because rind links s2n-bignum's constant table, which the
routine addresses PC-relative,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/edwards25519_scalarmulbase_alt.ml#L3870 -/
@[step]
axiom edwards25519_scalarmulbase_spec (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) :
    low.aarch64.edwards25519_scalarmulbase.edwards25519_scalarmulbase res scalar ⦃ r =>
      pairNat r.val = edModEncodePair (edPow edB (wordsNat scalar.val)) ⦄

/-- `EDWARDS25519_SCALARMULDOUBLE_ALT_SUBROUTINE_CORRECT`, whose `tables`
preconditions hold because rind links s2n-bignum's constant table, which the
routine addresses PC-relative,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/edwards25519_scalarmuldouble_alt.ml#L8432 -/
@[step]
axiom edwards25519_scalarmuldouble_spec (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) (point : Std.Array U64 8#usize)
    (bscalar : Std.Array U64 4#usize) :
    low.aarch64.edwards25519_scalarmuldouble.edwards25519_scalarmuldouble res scalar point
      bscalar ⦃ r =>
      ∀ P, edOnCurve P → edModDecodePair (pairNat point.val) = P →
        pairNat r.val =
          edModEncodePair (edMul (edPow P (wordsNat scalar.val)) (edPow edB (wordsNat bscalar.val))) ⦄

/-- `BIGNUM_MADD_N25519_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_madd_n25519_alt.ml#L829 -/
@[step]
axiom bignum_madd_n25519_spec (z x y c : Std.Array U64 4#usize) :
    low.aarch64.bignum_madd_n25519.bignum_madd_n25519 z x y c ⦃ r =>
      wordsNat r.val = (wordsNat x.val * wordsNat y.val + wordsNat c.val) % n25519 ⦄

/-- `BIGNUM_MOD_N25519_SUBROUTINE_CORRECT`, for the slice's length as `k`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_mod_n25519.ml#L434 -/
@[step]
axiom bignum_mod_n25519_spec (z : Std.Array U64 4#usize) (x : Slice U64) :
    low.aarch64.bignum_mod_n25519.bignum_mod_n25519 z x ⦃ r =>
      wordsNat r.val = wordsNat x.val % n25519 ⦄

/-- `BIGNUM_NEG_P25519_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_neg_p25519.ml#L90 -/
@[step]
axiom bignum_neg_p25519_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_neg_p25519.bignum_neg_p25519 z x ⦃ r =>
      wordsNat x.val ≤ p25519 → wordsNat r.val = (p25519 - wordsNat x.val) % p25519 ⦄

/-- `BIGNUM_LT_SUBROUTINE_CORRECT`, for the slices' lengths as `m` and `n`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_lt.ml#L346 -/
@[step]
axiom bignum_cmp_lt_spec (x y : Slice U64) :
    low.aarch64.bignum_cmp_lt.bignum_cmp_lt x y ⦃ r =>
      r.val = if wordsNat x.val < wordsNat y.val then 1 else 0 ⦄

/-! ### P-256

rind's aarch64 P-256 runs the `_alt` scalar multiplications and Montgomery
multiplication and squaring under the plain names, and the plain sources of
the other routines, which have no `_alt`. -/

/-- `p256_tabulates P 6 tab len tabulation`, for the table rind passes: entry
`j` of row `i`, counting entries from 1, represents `P` times 2⁶ⁱ·j. Its length
condition, (256 / 6 + 1) · 2⁵ · 64 ≤ len, is the type's 43 rows of 256 words,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_scalarmulbase_alt.ml#L3063 -/
def p256Tabulates (P : P256Point) (table : Std.Array (Std.Array U64 256#usize) 43#usize) : Prop :=
  ∀ i < 43, ∀ j, 1 ≤ j → j ≤ 32 →
    p256Represents2 (p256Pow P (2 ^ (6 * i) * j)) (pairNat ((table.val[i]!).val.drop (8 * (j - 1))))

/-- `BIGNUM_TOMONT_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_tomont_p256.ml#L415 -/
@[step]
axiom bignum_tomont_p256_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_tomont_p256.bignum_tomont_p256 z x ⦃ r =>
      wordsNat r.val = 2 ^ 256 * wordsNat x.val % p256 ⦄

/-- `BIGNUM_DEMONT_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_demont_p256.ml#L117 -/
@[step]
axiom bignum_demont_p256_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_demont_p256.bignum_demont_p256 z x ⦃ r =>
      wordsNat x.val < p256 → wordsNat r.val = p256RInv * wordsNat x.val % p256 ⦄

/-- `BIGNUM_ADD_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_add_p256.ml#L107 -/
@[step]
axiom bignum_add_p256_spec (z x y : Std.Array U64 4#usize) :
    low.aarch64.bignum_add_p256.bignum_add_p256 z x y ⦃ r =>
      wordsNat x.val < p256 → wordsNat y.val < p256 →
        wordsNat r.val = (wordsNat x.val + wordsNat y.val) % p256 ⦄

/-- `BIGNUM_MONTMUL_P256_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_montmul_p256_alt.ml#L239 -/
@[step]
axiom bignum_montmul_p256_spec (z x y : Std.Array U64 4#usize) :
    low.aarch64.bignum_montmul_p256.bignum_montmul_p256 z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val * wordsNat y.val % p256 ⦄

/-- `BIGNUM_MONTSQR_P256_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_montsqr_p256_alt.ml#L213 -/
@[step]
axiom bignum_montsqr_p256_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_montsqr_p256.bignum_montsqr_p256 z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val ^ 2 % p256 ⦄

/-- `BIGNUM_MOD_N256_4_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_mod_n256_4.ml#L110 -/
@[step]
axiom bignum_mod_n256_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_mod_n256.bignum_mod_n256 z x ⦃ r =>
      wordsNat r.val = wordsNat x.val % n256 ⦄

/-- `BIGNUM_INV_P256_SUBROUTINE_CORRECT`, with `inverse_mod p_256 n` stated
as what it is: the number below p that n times is 1 mod p,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_inv_p256.ml#L3120 -/
@[step]
axiom bignum_inv_p256_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_inv_p256.bignum_inv_p256 z x ⦃ r =>
      wordsNat r.val < p256 ∧
        (wordsNat x.val % p256 = 0 → wordsNat r.val = 0) ∧
        (wordsNat x.val % p256 ≠ 0 → wordsNat x.val * wordsNat r.val % p256 = 1) ⦄

/-- `BIGNUM_NEG_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_neg_p256.ml#L92 -/
@[step]
axiom bignum_neg_p256_spec (z x : Std.Array U64 4#usize) :
    low.aarch64.bignum_neg_p256.bignum_neg_p256 z x ⦃ r =>
      wordsNat x.val ≤ p256 → wordsNat r.val = (p256 - wordsNat x.val) % p256 ⦄

/-- The three coordinates at `xyz` as HOL Light's
`bignum_triple_from_memory (xyz,4)` reads them. -/
def tripleNat (xyz : List U64) : Nat × Nat × Nat :=
  (wordsNat (xyz.take 4), wordsNat ((xyz.drop 4).take 4), wordsNat ((xyz.drop 8).take 4))

/-- `weierstrass_of_jacobian (integer_mod_ring p_256) (x, y, z)`: infinity for
z of zero, and otherwise (x / z², y / z³) in the field of integers mod p, whose
inverses `ZMod`'s are,
https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/jacobian.ml#L21 -/
def p256OfJacobian (x y z : Nat) : P256Point :=
  if z = 0 then none
  else some (((x : ZMod p256) * ((z : ZMod p256) ^ 2)⁻¹).val, ((y : ZMod p256) * ((z : ZMod p256) ^ 3)⁻¹).val)

/-- `represents_p256 P (x, y, z)`: each coordinate is below p, and the
Jacobian point their Montgomery forms decode to (`montgomery_decode`) is `P`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_montjadd_alt.ml#L2505 -/
def p256Represents (P : P256Point) (xyz : Nat × Nat × Nat) : Prop :=
  xyz.1 < p256 ∧ xyz.2.1 < p256 ∧ xyz.2.2 < p256 ∧
    p256OfJacobian (p256RInv * xyz.1 % p256) (p256RInv * xyz.2.1 % p256)
      (p256RInv * xyz.2.2 % p256) = P

/-- `P256_MONTJADD_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_montjadd_alt.ml#L2677 -/
@[step]
axiom p256_montjadd_spec (p3 p1 p2 : Std.Array U64 12#usize) :
    low.aarch64.p256_montjadd.p256_montjadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents P2 (tripleNat p2.val) →
        (P1 = P2 → P2 = none) → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄

/-- `P256_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_montjdouble_alt.ml#L2341 -/
@[step]
axiom p256_montjdouble_spec (p3 p1 : Std.Array U64 12#usize) :
    low.aarch64.p256_montjdouble.p256_montjdouble p3 p1 ⦃ r =>
      ∀ P, p256Represents P (tripleNat p1.val) → p256Represents (p256Add P P) (tripleNat r.val) ⦄

/-- `P256_MONTJMIXADD_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_montjmixadd_alt.ml#L2104 -/
@[step]
axiom p256_montjmixadd_spec (p3 p1 : Std.Array U64 12#usize) (p2 : Std.Array U64 8#usize) :
    low.aarch64.p256_montjmixadd.p256_montjmixadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents2 P2 (pairNat p2.val) →
        P1 ≠ P2 → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄

/-! ### P-384 -/

/-- `BIGNUM_TOMONT_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_tomont_p384.ml#L501 -/
@[step]
axiom bignum_tomont_p384_spec (z x : Std.Array U64 6#usize) :
    low.aarch64.bignum_tomont_p384.bignum_tomont_p384 z x ⦃ r =>
      wordsNat r.val = 2 ^ 384 * wordsNat x.val % p384 ⦄

/-- `BIGNUM_DEMONT_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_demont_p384.ml#L424 -/
@[step]
axiom bignum_demont_p384_spec (z x : Std.Array U64 6#usize) :
    low.aarch64.bignum_demont_p384.bignum_demont_p384 z x ⦃ r =>
      wordsNat x.val < p384 → wordsNat r.val = p384RInv * wordsNat x.val % p384 ⦄

/-- `BIGNUM_ADD_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_add_p384.ml#L171 -/
@[step]
axiom bignum_add_p384_spec (z x y : Std.Array U64 6#usize) :
    low.aarch64.bignum_add_p384.bignum_add_p384 z x y ⦃ r =>
      wordsNat x.val < p384 → wordsNat y.val < p384 →
        wordsNat r.val = (wordsNat x.val + wordsNat y.val) % p384 ⦄

/-- `BIGNUM_MONTMUL_P384_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_montmul_p384_alt.ml#L447 -/
@[step]
axiom bignum_montmul_p384_spec (z x y : Std.Array U64 6#usize) :
    low.aarch64.bignum_montmul_p384.bignum_montmul_p384 z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val * wordsNat y.val % p384 ⦄

/-- `BIGNUM_MONTSQR_P384_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_montsqr_p384_alt.ml#L386 -/
@[step]
axiom bignum_montsqr_p384_spec (z x : Std.Array U64 6#usize) :
    low.aarch64.bignum_montsqr_p384.bignum_montsqr_p384 z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val ^ 2 % p384 ⦄

/-- `BIGNUM_INV_P384_SUBROUTINE_CORRECT`, with `inverse_mod p_384 n` stated
as what it is: the number below p that n times is 1 mod p,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_inv_p384.ml#L3433 -/
@[step]
axiom bignum_inv_p384_spec (z x : Std.Array U64 6#usize) :
    low.aarch64.bignum_inv_p384.bignum_inv_p384 z x ⦃ r =>
      wordsNat r.val < p384 ∧
        (wordsNat x.val % p384 = 0 → wordsNat r.val = 0) ∧
        (wordsNat x.val % p384 ≠ 0 → wordsNat x.val * wordsNat r.val % p384 = 1) ⦄

/-- `P384_MONTJSCALARMUL_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p384_montjscalarmul_alt.ml#L8917 -/
@[step]
axiom p384_montjscalarmul_spec (res : Std.Array U64 18#usize) (scalar : Std.Array U64 6#usize)
    (point : Std.Array U64 18#usize) :
    low.aarch64.p384_montjscalarmul.p384_montjscalarmul res scalar point ⦃ r =>
      ∀ P, p384OnCurve P → p384Represents P (tripleNat6 point.val) →
        p384Represents (p384Pow P (wordsNat scalar.val)) (tripleNat6 r.val) ⦄

/-! ### Generic modular arithmetic

Each routine reads its inputs at the result's length `k`, so a theorem
assumes the inputs have it, and its `&mut` result keeps it, as Rust's do.
`inverse_mod m (2^(64k))` is stated as what it is, for odd `m`: any `i` with
2^(64k)·i ≡ 1 (mod m), which are all congruent. -/

/-- `BIGNUM_MODADD_SUBROUTINE_CORRECT`, whose precondition that each input is
below `m` the theorem's callers establish,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_modadd.ml#L319 -/
@[step]
axiom bignum_modadd_spec (z x y m : Slice U64) (hx : x.length = z.length)
    (hy : y.length = z.length) (hm : m.length = z.length)
    (ha : wordsNat x.val < wordsNat m.val) (hb : wordsNat y.val < wordsNat m.val) :
    low.aarch64.bignum_modadd.bignum_modadd z x y m ⦃ r =>
      r.length = z.length ∧ wordsNat r.val = (wordsNat x.val + wordsNat y.val) % wordsNat m.val ⦄

/-- `BIGNUM_MONTMUL_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_montmul.ml#L844 -/
@[step]
axiom bignum_montmul_spec (z x y m : Slice U64) (hx : x.length = z.length)
    (hy : y.length = z.length) (hm : m.length = z.length) :
    low.aarch64.bignum_montmul.bignum_montmul z x y m ⦃ r =>
      r.length = z.length ∧
        (wordsNat m.val % 2 = 1 → wordsNat x.val * wordsNat y.val ≤ 2 ^ (64 * z.length) * wordsNat m.val →
          ∀ i, 2 ^ (64 * z.length) * i % wordsNat m.val = 1 % wordsNat m.val →
            wordsNat r.val = i * wordsNat x.val * wordsNat y.val % wordsNat m.val) ⦄

/-- `BIGNUM_DEMONT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_demont.ml#L672 -/
@[step]
axiom bignum_demont_spec (z x m : Slice U64) (hx : x.length = z.length)
    (hm : m.length = z.length) :
    low.aarch64.bignum_demont.bignum_demont z x m ⦃ r =>
      r.length = z.length ∧
        (wordsNat m.val % 2 = 1 →
          ∀ i, 2 ^ (64 * z.length) * i % wordsNat m.val = 1 % wordsNat m.val →
            wordsNat r.val = i * wordsNat x.val % wordsNat m.val) ⦄

/-- `BIGNUM_MODINV_SUBROUTINE_CORRECT`, with its temporary buffer `w` of at
least 3k words,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/bignum_modinv.ml#L4890 -/
@[step]
axiom bignum_modinv_spec (z a b w : Slice U64) (ha : a.length = z.length)
    (hb : b.length = z.length) (hw : 3 * z.length ≤ w.length) :
    low.aarch64.bignum_modinv.bignum_modinv z a b w ⦃ r =>
      r.1.length = z.length ∧
        (Nat.Coprime (wordsNat a.val) (wordsNat b.val) → wordsNat b.val % 2 = 1 → wordsNat b.val ≠ 1 →
          wordsNat r.1.val < wordsNat b.val ∧ wordsNat a.val * wordsNat r.1.val % wordsNat b.val = 1) ⦄

/-- `P256_SCALARMUL_ALT_SUBROUTINE_CORRECT`, whose stack frame is 1248 bytes,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_scalarmul_alt.ml#L7459 -/
@[step]
axiom p256_scalarmul_spec (res : Std.Array U64 8#usize) (scalar : Std.Array U64 4#usize)
    (point : Std.Array U64 8#usize) :
    low.aarch64.p256_scalarmul.p256_scalarmul res scalar point ⦃ r =>
      ∀ P, p256OnCurve P → p256Affine (pairNat point.val) P →
        p256AffineZ (pairNat r.val) (p256Pow P (wordsNat scalar.val)) ⦄

/-- `P256_SCALARMULBASE_ALT_SUBROUTINE_CORRECT`, with the block size 6 the
wrapper passes and a table it reads but cannot overlap,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/p256_scalarmulbase_alt.ml#L4059 -/
@[step]
axiom p256_scalarmulbase_spec (res : Std.Array U64 8#usize) (scalar : Std.Array U64 4#usize)
    (table : Std.Array (Std.Array U64 256#usize) 43#usize) :
    low.aarch64.p256_scalarmulbase.p256_scalarmulbase res scalar table ⦃ r =>
      ∀ P, p256OnCurve P → p256Tabulates P table →
        p256AffineZ (pairNat r.val) (p256Pow P (wordsNat scalar.val)) ⦄

/-! ### Keccak-f[1600]

Each routine permutes the 25-lane states it is given in place, for the round
constants rind passes. -/

/-- `SHA3_KECCAK_F1600_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/sha3_keccak_f1600.ml#L460 -/
axiom sha3_keccak_f1600_spec (a : Std.Array U64 25#usize) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.aarch64.sha3_keccak_f1600.sha3_keccak_f1600 a rc ⦃ r =>
      r.val.map (·.bv) = keccak 24 (a.val.map (·.bv)) ⦄

/-- `SHA3_KECCAK_F1600_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/sha3_keccak_f1600_alt.ml#L245 -/
axiom sha3_keccak_f1600_alt_spec (a : Std.Array U64 25#usize) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.aarch64.sha3_keccak_f1600_alt.sha3_keccak_f1600 a rc ⦃ r =>
      r.val.map (·.bv) = keccak 24 (a.val.map (·.bv)) ⦄

/-- `SHA3_KECCAK2_F1600_SUBROUTINE_CORRECT`, whose two states are consecutive,
as an array of them is,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/arm/proofs/sha3_keccak2_f1600.ml#L313 -/
axiom sha3_keccak2_f1600_spec (a : Std.Array (Std.Array U64 25#usize) 2#usize)
    (rc : Std.Array U64 24#usize) (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.aarch64.sha3_keccak2_f1600.sha3_keccak2_f1600 a rc ⦃ r =>
      r.val.map (·.val.map (·.bv)) = (a.val.map (·.val.map (·.bv))).map (keccak 24) ⦄

/-- rind runs on this CPU: its entry guards' CPU-feature checks pass. Neither
reads an input. -/
def Runs : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ (∃ e, low.entry.Entry.new_public = ok e)

/-- Ed25519 verification's double scalar multiplication runs s2n-bignum's
routine, as it does on every aarch64 CPU. -/
def RunsDouble : Prop := True

@[step]
theorem new_secret_spec (h : Runs) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

@[step]
theorem new_public_spec (h : Runs) : low.entry.Entry.new_public ⦃ _ => True ⦄ := by
  obtain ⟨-, ⟨e, he⟩⟩ := h
  simp [he]

end rind.aarch64
