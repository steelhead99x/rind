import Rind.X86_64.Funs
import Rind.Spec
import Rind.Ed25519
import Mathlib.Data.Nat.Size
import Rind.Keccak
import Rind.Nist
open Aeneas Aeneas.Std Result rind.spec

/-!
# s2n-bignum's contracts on x86_64

Each axiom restates one of s2n-bignum's HOL Light theorems, at the revision
rind transliterates (b4f17ee7), about the opaque Rust wrapper
`admin/parse-asm` generates around that routine. The theorem's preconditions
hold for every call from safe Rust: the `&mut` result cannot overlap an input
or the routine's code, and the routine's stack lies below the caller's
frame. Its total correctness (`ensures`) gives the `ok`.

The restatement, and that rind's inline assembly is s2n-bignum's object code
with the wrapper passing the arguments the theorem names, are trusted.
-/

namespace rind.x86_64

/-- `CURVE25519_X25519_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/curve25519_x25519.ml#L8305 -/
@[step]
axiom curve25519_x25519_spec (res scalar point : Std.Array U64 4#usize) :
    low.x86_64.curve25519_x25519.curve25519_x25519 res scalar point ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) (wordsNat point.val) ⦄

/-- `CURVE25519_X25519_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/curve25519_x25519_alt.ml#L8524 -/
@[step]
axiom curve25519_x25519_alt_spec (res scalar point : Std.Array U64 4#usize) :
    low.x86_64.curve25519_x25519_alt.curve25519_x25519_alt res scalar point ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) (wordsNat point.val) ⦄

/-- `CURVE25519_X25519BASE_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/curve25519_x25519base.ml#L5099 -/
@[step]
axiom curve25519_x25519base_spec (res scalar : Std.Array U64 4#usize) :
    low.x86_64.curve25519_x25519base.curve25519_x25519base res scalar ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) 9 ⦄

/-- `CURVE25519_X25519BASE_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/curve25519_x25519base_alt.ml#L5197 -/
@[step]
axiom curve25519_x25519base_alt_spec (res scalar : Std.Array U64 4#usize) :
    low.x86_64.curve25519_x25519base_alt.curve25519_x25519base_alt res scalar ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) 9 ⦄

/-- `BIGNUM_EQ_SUBROUTINE_CORRECT`, whose 1 or 0 the wrapper returns as
`true` or `false`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_eq.ml#L294 -/
@[step]
axiom bignum_eq_spec (x y : Slice U64) :
    low.x86_64.bignum_eq.bignum_eq x y ⦃ b => b = decide (wordsNat x.val = wordsNat y.val) ⦄

/-! ### Ed25519 -/

/-- `EDWARDS25519_DECODE_SUBROUTINE_CORRECT`, whose 0 for a valid
encoding the wrapper returns as `true`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/edwards25519_decode.ml#L2128 -/
@[step]
axiom edwards25519_decode_spec (z : Std.Array U64 8#usize) (c : Std.Array U8 32#usize) :
    low.x86_64.edwards25519_decode.edwards25519_decode z c ⦃ r =>
      (r.1 = true ↔ edValidEncode (leNat c.val)) ∧
        (edValidEncode (leNat c.val) → pairNat r.2.val = edModEncodePair (edDecode (leNat c.val))) ⦄

/-- `EDWARDS25519_SCALARMULBASE_SUBROUTINE_CORRECT`, whose `tables`
preconditions hold because rind links s2n-bignum's constant table, which the
routine addresses PC-relative,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/edwards25519_scalarmulbase.ml#L5312 -/
@[step]
axiom edwards25519_scalarmulbase_spec (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) :
    low.x86_64.edwards25519_scalarmulbase.edwards25519_scalarmulbase res scalar ⦃ r =>
      pairNat r.val = edModEncodePair (edPow edB (wordsNat scalar.val)) ⦄

/-- `EDWARDS25519_SCALARMULDOUBLE_SUBROUTINE_CORRECT`, whose `tables`
preconditions hold because rind links s2n-bignum's constant table, which the
routine addresses PC-relative,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/edwards25519_scalarmuldouble.ml#L11800 -/
@[step]
axiom edwards25519_scalarmuldouble_spec (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) (point : Std.Array U64 8#usize)
    (bscalar : Std.Array U64 4#usize) :
    low.x86_64.edwards25519_scalarmuldouble.edwards25519_scalarmuldouble res scalar point
      bscalar ⦃ r =>
      ∀ P, edOnCurve P → edModDecodePair (pairNat point.val) = P →
        pairNat r.val =
          edModEncodePair (edMul (edPow P (wordsNat scalar.val)) (edPow edB (wordsNat bscalar.val))) ⦄

/-- `BIGNUM_MADD_N25519_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_madd_n25519.ml#L964 -/
@[step]
axiom bignum_madd_n25519_spec (z x y c : Std.Array U64 4#usize) :
    low.x86_64.bignum_madd_n25519.bignum_madd_n25519 z x y c ⦃ r =>
      wordsNat r.val = (wordsNat x.val * wordsNat y.val + wordsNat c.val) % n25519 ⦄

/-- `EDWARDS25519_DECODE_ALT_SUBROUTINE_CORRECT`, whose 0 for a valid
encoding the wrapper returns as `true`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/edwards25519_decode_alt.ml#L2071 -/
@[step]
axiom edwards25519_decode_alt_spec (z : Std.Array U64 8#usize) (c : Std.Array U8 32#usize) :
    low.x86_64.edwards25519_decode_alt.edwards25519_decode_alt z c ⦃ r =>
      (r.1 = true ↔ edValidEncode (leNat c.val)) ∧
        (edValidEncode (leNat c.val) → pairNat r.2.val = edModEncodePair (edDecode (leNat c.val))) ⦄

/-- `EDWARDS25519_SCALARMULBASE_ALT_SUBROUTINE_CORRECT`, whose `tables`
preconditions hold because rind links s2n-bignum's constant table, which the
routine addresses PC-relative,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/edwards25519_scalarmulbase_alt.ml#L5418 -/
@[step]
axiom edwards25519_scalarmulbase_alt_spec (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) :
    low.x86_64.edwards25519_scalarmulbase_alt.edwards25519_scalarmulbase_alt res scalar ⦃ r =>
      pairNat r.val = edModEncodePair (edPow edB (wordsNat scalar.val)) ⦄

/-- `EDWARDS25519_SCALARMULDOUBLE_ALT_SUBROUTINE_CORRECT`, whose `tables`
preconditions hold because rind links s2n-bignum's constant table, which the
routine addresses PC-relative,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/edwards25519_scalarmuldouble_alt.ml#L11872 -/
@[step]
axiom edwards25519_scalarmuldouble_alt_spec (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) (point : Std.Array U64 8#usize)
    (bscalar : Std.Array U64 4#usize) :
    low.x86_64.edwards25519_scalarmuldouble_alt.edwards25519_scalarmuldouble_alt res scalar point
      bscalar ⦃ r =>
      ∀ P, edOnCurve P → edModDecodePair (pairNat point.val) = P →
        pairNat r.val =
          edModEncodePair (edMul (edPow P (wordsNat scalar.val)) (edPow edB (wordsNat bscalar.val))) ⦄

/-- `BIGNUM_MADD_N25519_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_madd_n25519_alt.ml#L939 -/
@[step]
axiom bignum_madd_n25519_alt_spec (z x y c : Std.Array U64 4#usize) :
    low.x86_64.bignum_madd_n25519_alt.bignum_madd_n25519_alt z x y c ⦃ r =>
      wordsNat r.val = (wordsNat x.val * wordsNat y.val + wordsNat c.val) % n25519 ⦄

/-- `BIGNUM_MOD_N25519_SUBROUTINE_CORRECT`, for the slice's length as `k`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_mod_n25519.ml#L498 -/
@[step]
axiom bignum_mod_n25519_spec (z : Std.Array U64 4#usize) (x : Slice U64) :
    low.x86_64.bignum_mod_n25519.bignum_mod_n25519 z x ⦃ r =>
      wordsNat r.val = wordsNat x.val % n25519 ⦄

/-- `BIGNUM_NEG_P25519_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_neg_p25519.ml#L120 -/
@[step]
axiom bignum_neg_p25519_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_neg_p25519.bignum_neg_p25519 z x ⦃ r =>
      wordsNat x.val ≤ p25519 → wordsNat r.val = (p25519 - wordsNat x.val) % p25519 ⦄

/-- `BIGNUM_LT_SUBROUTINE_CORRECT`, for the slices' lengths as `m` and `n`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_lt.ml#L412 -/
@[step]
axiom bignum_cmp_lt_spec (x y : Slice U64) :
    low.x86_64.bignum_cmp_lt.bignum_cmp_lt x y ⦃ r =>
      r.val = if wordsNat x.val < wordsNat y.val then 1 else 0 ⦄

/-! ### Keccak-f[1600]

Each routine permutes the 25-lane states it is given in place, for the round
constants, and the four-way one's byte-shuffle constants, that rind passes. -/

/-- `SHA3_KECCAK_F1600_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/sha3_keccak_f1600.ml#L736 -/
axiom sha3_keccak_f1600_spec (a : Std.Array U64 25#usize) (rc : Std.Array U64 24#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants) :
    low.x86_64.sha3_keccak_f1600.sha3_keccak_f1600 a rc ⦃ r =>
      r.val.map (·.bv) = keccak 24 (a.val.map (·.bv)) ⦄

/-- `SHA3_KECCAK4_F1600_ALT_SUBROUTINE_CORRECT`, whose four states are
consecutive, as an array of them is,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/sha3_keccak4_f1600_alt.ml#L1081 -/
axiom sha3_keccak4_f1600_alt_spec (a : Std.Array (Std.Array U64 25#usize) 4#usize)
    (rc : Std.Array U64 24#usize) (rho8 rho56 : Std.Array U64 4#usize)
    (hrc : rc.val.map (·.bv) = keccakRoundConstants) (h8 : rho8.val.map (·.bv) = keccakRho8)
    (h56 : rho56.val.map (·.bv) = keccakRho56) :
    low.x86_64.sha3_keccak4_f1600_alt.sha3_keccak4_f1600 a rc rho8 rho56 ⦃ r =>
      r.val.map (·.val.map (·.bv)) = (a.val.map (·.val.map (·.bv))).map (keccak 24) ⦄

/-! ### P-256 -/

/-- `BIGNUM_TOMONT_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_tomont_p256.ml#L373 -/
@[step]
axiom bignum_tomont_p256_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_tomont_p256.bignum_tomont_p256 z x ⦃ r =>
      wordsNat r.val = 2 ^ 256 * wordsNat x.val % p256 ⦄

/-- `BIGNUM_TOMONT_P256_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_tomont_p256_alt.ml#L329 -/
@[step]
axiom bignum_tomont_p256_alt_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_tomont_p256_alt.bignum_tomont_p256_alt z x ⦃ r =>
      wordsNat r.val = 2 ^ 256 * wordsNat x.val % p256 ⦄

/-- `BIGNUM_DEMONT_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_demont_p256.ml#L185 -/
@[step]
axiom bignum_demont_p256_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_demont_p256.bignum_demont_p256 z x ⦃ r =>
      wordsNat x.val < p256 → wordsNat r.val = p256RInv * wordsNat x.val % p256 ⦄

/-- `BIGNUM_DEMONT_P256_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_demont_p256_alt.ml#L171 -/
@[step]
axiom bignum_demont_p256_alt_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_demont_p256_alt.bignum_demont_p256_alt z x ⦃ r =>
      wordsNat x.val < p256 → wordsNat r.val = p256RInv * wordsNat x.val % p256 ⦄

/-- `BIGNUM_ADD_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_add_p256.ml#L153 -/
@[step]
axiom bignum_add_p256_spec (z x y : Std.Array U64 4#usize) :
    low.x86_64.bignum_add_p256.bignum_add_p256 z x y ⦃ r =>
      wordsNat x.val < p256 → wordsNat y.val < p256 →
        wordsNat r.val = (wordsNat x.val + wordsNat y.val) % p256 ⦄

/-- `BIGNUM_MONTMUL_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montmul_p256.ml#L344 -/
@[step]
axiom bignum_montmul_p256_spec (z x y : Std.Array U64 4#usize) :
    low.x86_64.bignum_montmul_p256.bignum_montmul_p256 z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val * wordsNat y.val % p256 ⦄

/-- `BIGNUM_MONTMUL_P256_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montmul_p256_alt.ml#L336 -/
@[step]
axiom bignum_montmul_p256_alt_spec (z x y : Std.Array U64 4#usize) :
    low.x86_64.bignum_montmul_p256_alt.bignum_montmul_p256_alt z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val * wordsNat y.val % p256 ⦄

/-- `BIGNUM_MONTSQR_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montsqr_p256.ml#L324 -/
@[step]
axiom bignum_montsqr_p256_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_montsqr_p256.bignum_montsqr_p256 z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val ^ 2 % p256 ⦄

/-- `BIGNUM_MONTSQR_P256_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montsqr_p256_alt.ml#L304 -/
@[step]
axiom bignum_montsqr_p256_alt_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_montsqr_p256_alt.bignum_montsqr_p256_alt z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val ^ 2 % p256 ⦄

/-- `P256_SCALARMUL_SUBROUTINE_CORRECT`, whose stack frame is 1368 bytes,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_scalarmul.ml#L11839 -/
@[step]
axiom p256_scalarmul_spec (res : Std.Array U64 8#usize) (scalar : Std.Array U64 4#usize)
    (point : Std.Array U64 8#usize) :
    low.x86_64.p256_scalarmul.p256_scalarmul res scalar point ⦃ r =>
      ∀ P, p256OnCurve P → p256Affine (pairNat point.val) P →
        p256AffineZ (pairNat r.val) (p256Pow P (wordsNat scalar.val)) ⦄

/-- `P256_SCALARMUL_ALT_SUBROUTINE_CORRECT`, whose stack frame is 1368 bytes,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_scalarmul_alt.ml#L11464 -/
@[step]
axiom p256_scalarmul_alt_spec (res : Std.Array U64 8#usize) (scalar : Std.Array U64 4#usize)
    (point : Std.Array U64 8#usize) :
    low.x86_64.p256_scalarmul_alt.p256_scalarmul_alt res scalar point ⦃ r =>
      ∀ P, p256OnCurve P → p256Affine (pairNat point.val) P →
        p256AffineZ (pairNat r.val) (p256Pow P (wordsNat scalar.val)) ⦄

/-- `BIGNUM_MOD_N256_4_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_mod_n256_4.ml#L140 -/
@[step]
axiom bignum_mod_n256_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_mod_n256.bignum_mod_n256 z x ⦃ r =>
      wordsNat r.val = wordsNat x.val % n256 ⦄

/-- `BIGNUM_INV_P256_SUBROUTINE_CORRECT`, with `inverse_mod p_256 n` stated
as what it is: the number below p that n times is 1 mod p,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_inv_p256.ml#L3950 -/
@[step]
axiom bignum_inv_p256_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_inv_p256.bignum_inv_p256 z x ⦃ r =>
      wordsNat r.val < p256 ∧
        (wordsNat x.val % p256 = 0 → wordsNat r.val = 0) ∧
        (wordsNat x.val % p256 ≠ 0 → wordsNat x.val * wordsNat r.val % p256 = 1) ⦄

/-- `BIGNUM_NEG_P256_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_neg_p256.ml#L124 -/
@[step]
axiom bignum_neg_p256_spec (z x : Std.Array U64 4#usize) :
    low.x86_64.bignum_neg_p256.bignum_neg_p256 z x ⦃ r =>
      wordsNat x.val ≤ p256 → wordsNat r.val = (p256 - wordsNat x.val) % p256 ⦄

/-- `P256_MONTJADD_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_montjadd.ml#L4071 -/
@[step]
axiom p256_montjadd_spec (p3 p1 p2 : Std.Array U64 12#usize) :
    low.x86_64.p256_montjadd.p256_montjadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents P2 (tripleNat p2.val) →
        (P1 = P2 → P2 = none) → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄

/-- `P256_MONTJADD_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_montjadd_alt.ml#L3879 -/
@[step]
axiom p256_montjadd_alt_spec (p3 p1 p2 : Std.Array U64 12#usize) :
    low.x86_64.p256_montjadd_alt.p256_montjadd_alt p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents P2 (tripleNat p2.val) →
        (P1 = P2 → P2 = none) → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄

/-- `P256_MONTJDOUBLE_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_montjdouble.ml#L3160 -/
@[step]
axiom p256_montjdouble_spec (p3 p1 : Std.Array U64 12#usize) :
    low.x86_64.p256_montjdouble.p256_montjdouble p3 p1 ⦃ r =>
      ∀ P, p256Represents P (tripleNat p1.val) → p256Represents (p256Add P P) (tripleNat r.val) ⦄

/-- `P256_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_montjdouble_alt.ml#L3085 -/
@[step]
axiom p256_montjdouble_alt_spec (p3 p1 : Std.Array U64 12#usize) :
    low.x86_64.p256_montjdouble_alt.p256_montjdouble_alt p3 p1 ⦃ r =>
      ∀ P, p256Represents P (tripleNat p1.val) → p256Represents (p256Add P P) (tripleNat r.val) ⦄

/-- `P256_MONTJMIXADD_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_montjmixadd.ml#L3104 -/
@[step]
axiom p256_montjmixadd_spec (p3 p1 : Std.Array U64 12#usize) (p2 : Std.Array U64 8#usize) :
    low.x86_64.p256_montjmixadd.p256_montjmixadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents2 P2 (pairNat p2.val) →
        P1 ≠ P2 → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄

/-- `P256_MONTJMIXADD_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p256_montjmixadd_alt.ml#L2940 -/
@[step]
axiom p256_montjmixadd_alt_spec (p3 p1 : Std.Array U64 12#usize) (p2 : Std.Array U64 8#usize) :
    low.x86_64.p256_montjmixadd_alt.p256_montjmixadd_alt p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents2 P2 (pairNat p2.val) →
        P1 ≠ P2 → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄

/-- `BIGNUM_MUX_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_mux.ml#L141 -/
@[step]
axiom bignum_mux_spec (p : U64) (z x y : Slice U64) (hx : x.length = z.length)
    (hy : y.length = z.length) :
    low.x86_64.bignum_mux.bignum_mux p z x y ⦃ r =>
      r.length = z.length ∧ wordsNat r.val = if p.val ≠ 0 then wordsNat x.val else wordsNat y.val ⦄

/-! ### P-256's generator multiplication

PLACEHOLDER until the HOL Light proof of aws-lc's mixed addition lands. -/

/-- What aws-lc's `ecp_nistz256_point_add_affine` and `_affinex` compute,
in place, for coordinates below p: `p1` itself when `p2` is all zeros, the
affine infinity; `p2` with a Montgomery-form z of one when `p1`'s z is zero,
the Jacobian infinity; and otherwise the sum of the points they represent,
unless those are equal, which it cannot double. -/
@[step]
axiom p256_point_add_affine_spec (p1 : Std.Array U64 12#usize) (p2 : Std.Array U64 8#usize) :
    low.x86_64.ecp_nistz256.p256_point_add_affine p1 p2 ⦃ r =>
      (tripleNat p1.val).1 < p256 → (tripleNat p1.val).2.1 < p256 → (tripleNat p1.val).2.2 < p256 →
      (pairNat p2.val).1 < p256 → (pairNat p2.val).2 < p256 →
        (pairNat p2.val = (0, 0) → tripleNat r.val = tripleNat p1.val) ∧
        (pairNat p2.val ≠ (0, 0) → (tripleNat p1.val).2.2 = 0 →
          tripleNat r.val = ((pairNat p2.val).1, (pairNat p2.val).2, 2 ^ 256 % p256)) ∧
        (pairNat p2.val ≠ (0, 0) → (tripleNat p1.val).2.2 ≠ 0 →
          ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents2 P2 (pairNat p2.val) →
            P1 ≠ P2 → p256Represents (p256Add P1 P2) (tripleNat r.val)) ⦄

/-! ### P-384 -/

/-- `BIGNUM_TOMONT_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_tomont_p384.ml#L545 -/
@[step]
axiom bignum_tomont_p384_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_tomont_p384.bignum_tomont_p384 z x ⦃ r =>
      wordsNat r.val = 2 ^ 384 * wordsNat x.val % p384 ⦄

/-- `BIGNUM_TOMONT_P384_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_tomont_p384_alt.ml#L528 -/
@[step]
axiom bignum_tomont_p384_alt_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_tomont_p384_alt.bignum_tomont_p384_alt z x ⦃ r =>
      wordsNat r.val = 2 ^ 384 * wordsNat x.val % p384 ⦄

/-- `BIGNUM_DEMONT_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_demont_p384.ml#L294 -/
@[step]
axiom bignum_demont_p384_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_demont_p384.bignum_demont_p384 z x ⦃ r =>
      wordsNat x.val < p384 → wordsNat r.val = p384RInv * wordsNat x.val % p384 ⦄

/-- `BIGNUM_DEMONT_P384_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_demont_p384_alt.ml#L292 -/
@[step]
axiom bignum_demont_p384_alt_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_demont_p384_alt.bignum_demont_p384_alt z x ⦃ r =>
      wordsNat x.val < p384 → wordsNat r.val = p384RInv * wordsNat x.val % p384 ⦄

/-- `BIGNUM_ADD_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_add_p384.ml#L172 -/
@[step]
axiom bignum_add_p384_spec (z x y : Std.Array U64 6#usize) :
    low.x86_64.bignum_add_p384.bignum_add_p384 z x y ⦃ r =>
      wordsNat x.val < p384 → wordsNat y.val < p384 →
        wordsNat r.val = (wordsNat x.val + wordsNat y.val) % p384 ⦄

/-- `BIGNUM_MONTMUL_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montmul_p384.ml#L609 -/
@[step]
axiom bignum_montmul_p384_spec (z x y : Std.Array U64 6#usize) :
    low.x86_64.bignum_montmul_p384.bignum_montmul_p384 z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val * wordsNat y.val % p384 ⦄

/-- `BIGNUM_MONTMUL_P384_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montmul_p384_alt.ml#L596 -/
@[step]
axiom bignum_montmul_p384_alt_spec (z x y : Std.Array U64 6#usize) :
    low.x86_64.bignum_montmul_p384_alt.bignum_montmul_p384_alt z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val * wordsNat y.val % p384 ⦄

/-- `BIGNUM_MONTSQR_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montsqr_p384.ml#L548 -/
@[step]
axiom bignum_montsqr_p384_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_montsqr_p384.bignum_montsqr_p384 z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val ^ 2 % p384 ⦄

/-- `BIGNUM_MONTSQR_P384_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montsqr_p384_alt.ml#L516 -/
@[step]
axiom bignum_montsqr_p384_alt_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_montsqr_p384_alt.bignum_montsqr_p384_alt z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val ^ 2 % p384 ⦄

/-- `BIGNUM_INV_P384_SUBROUTINE_CORRECT`, with `inverse_mod p_384 n` stated
as what it is: the number below p that n times is 1 mod p,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_inv_p384.ml#L4341 -/
@[step]
axiom bignum_inv_p384_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_inv_p384.bignum_inv_p384 z x ⦃ r =>
      wordsNat r.val < p384 ∧
        (wordsNat x.val % p384 = 0 → wordsNat r.val = 0) ∧
        (wordsNat x.val % p384 ≠ 0 → wordsNat x.val * wordsNat r.val % p384 = 1) ⦄

/-- `P384_MONTJSCALARMUL_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p384_montjscalarmul.ml#L13042 -/
@[step]
axiom p384_montjscalarmul_spec (res : Std.Array U64 18#usize) (scalar : Std.Array U64 6#usize)
    (point : Std.Array U64 18#usize) :
    low.x86_64.p384_montjscalarmul.p384_montjscalarmul res scalar point ⦃ r =>
      ∀ P, p384OnCurve P → p384Represents P (tripleNat6 point.val) →
        p384Represents (p384Pow P (wordsNat scalar.val)) (tripleNat6 r.val) ⦄

/-- `P384_MONTJSCALARMUL_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p384_montjscalarmul_alt.ml#L13307 -/
@[step]
axiom p384_montjscalarmul_alt_spec (res : Std.Array U64 18#usize) (scalar : Std.Array U64 6#usize)
    (point : Std.Array U64 18#usize) :
    low.x86_64.p384_montjscalarmul_alt.p384_montjscalarmul_alt res scalar point ⦃ r =>
      ∀ P, p384OnCurve P → p384Represents P (tripleNat6 point.val) →
        p384Represents (p384Pow P (wordsNat scalar.val)) (tripleNat6 r.val) ⦄

/-- `P384_MONTJDOUBLE_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p384_montjdouble.ml#L4854 -/
@[step]
axiom p384_montjdouble_spec (p3 p1 : Std.Array U64 18#usize) :
    low.x86_64.p384_montjdouble.p384_montjdouble p3 p1 ⦃ r =>
      ∀ P, p384Represents P (tripleNat6 p1.val) → p384Represents (p384Add P P) (tripleNat6 r.val) ⦄

/-- `P384_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p384_montjdouble_alt.ml#L4845 -/
@[step]
axiom p384_montjdouble_alt_spec (p3 p1 : Std.Array U64 18#usize) :
    low.x86_64.p384_montjdouble_alt.p384_montjdouble_alt p3 p1 ⦃ r =>
      ∀ P, p384Represents P (tripleNat6 p1.val) → p384Represents (p384Add P P) (tripleNat6 r.val) ⦄

/-- `P384_MONTJMIXADD_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p384_montjmixadd.ml#L5505 -/
@[step]
axiom p384_montjmixadd_spec (p3 p1 : Std.Array U64 18#usize) (p2 : Std.Array U64 12#usize) :
    low.x86_64.p384_montjmixadd.p384_montjmixadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p384Represents P1 (tripleNat6 p1.val) → p384Represents2 P2 (pairNat6 p2.val) →
        P1 ≠ P2 → p384Represents (p384Add P1 P2) (tripleNat6 r.val) ⦄

/-- `P384_MONTJMIXADD_ALT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/p384_montjmixadd_alt.ml#L5607 -/
@[step]
axiom p384_montjmixadd_alt_spec (p3 p1 : Std.Array U64 18#usize) (p2 : Std.Array U64 12#usize) :
    low.x86_64.p384_montjmixadd_alt.p384_montjmixadd_alt p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p384Represents P1 (tripleNat6 p1.val) → p384Represents2 P2 (pairNat6 p2.val) →
        P1 ≠ P2 → p384Represents (p384Add P1 P2) (tripleNat6 r.val) ⦄

/-- `BIGNUM_NEG_P384_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_neg_p384.ml#L131 -/
@[step]
axiom bignum_neg_p384_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_neg_p384.bignum_neg_p384 z x ⦃ r =>
      wordsNat x.val ≤ p384 → wordsNat r.val = (p384 - wordsNat x.val) % p384 ⦄

/-- `BIGNUM_MOD_N384_6_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_mod_n384_6.ml#L162 -/
@[step]
axiom bignum_mod_n384_spec (z x : Std.Array U64 6#usize) :
    low.x86_64.bignum_mod_n384.bignum_mod_n384 z x ⦃ r => wordsNat r.val = wordsNat x.val % n384 ⦄

/-! ### Generic modular arithmetic

ECDSA's scalar arithmetic mod n. Each routine reads its inputs at the
result's length `k`, so a theorem assumes the inputs have it, and its `&mut`
result keeps it, as Rust's do. `inverse_mod m (2^(64k))` is stated as what it
is, for odd `m`: any `i` with 2^(64k)·i ≡ 1 (mod m), which are all congruent. -/

/-- `BIGNUM_MODADD_SUBROUTINE_CORRECT`, whose precondition that each input is
below `m` the theorem's callers establish,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_modadd.ml#L350 -/
@[step]
axiom bignum_modadd_spec (z x y m : Slice U64) (hx : x.length = z.length)
    (hy : y.length = z.length) (hm : m.length = z.length)
    (ha : wordsNat x.val < wordsNat m.val) (hb : wordsNat y.val < wordsNat m.val) :
    low.x86_64.bignum_modadd.bignum_modadd z x y m ⦃ r =>
      r.length = z.length ∧ wordsNat r.val = (wordsNat x.val + wordsNat y.val) % wordsNat m.val ⦄

/-- `BIGNUM_MONTMUL_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_montmul.ml#L974 -/
@[step]
axiom bignum_montmul_spec (z x y m : Slice U64) (hx : x.length = z.length)
    (hy : y.length = z.length) (hm : m.length = z.length) :
    low.x86_64.bignum_montmul.bignum_montmul z x y m ⦃ r =>
      r.length = z.length ∧
        (wordsNat m.val % 2 = 1 → wordsNat x.val * wordsNat y.val ≤ 2 ^ (64 * z.length) * wordsNat m.val →
          ∀ i, 2 ^ (64 * z.length) * i % wordsNat m.val = 1 % wordsNat m.val →
            wordsNat r.val = i * wordsNat x.val * wordsNat y.val % wordsNat m.val) ⦄

/-- `BIGNUM_DEMONT_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_demont.ml#L762 -/
@[step]
axiom bignum_demont_spec (z x m : Slice U64) (hx : x.length = z.length)
    (hm : m.length = z.length) :
    low.x86_64.bignum_demont.bignum_demont z x m ⦃ r =>
      r.length = z.length ∧
        (wordsNat m.val % 2 = 1 →
          ∀ i, 2 ^ (64 * z.length) * i % wordsNat m.val = 1 % wordsNat m.val →
            wordsNat r.val = i * wordsNat x.val % wordsNat m.val) ⦄

/-- `BIGNUM_MODINV_SUBROUTINE_CORRECT`, with its temporary buffer `w` of at
least 3k words,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_modinv.ml#L4793 -/
@[step]
axiom bignum_modinv_spec (z a b w : Slice U64) (ha : a.length = z.length)
    (hb : b.length = z.length) (hw : 3 * z.length ≤ w.length)
    (hk : z.length < 2 ^ 57) :
    low.x86_64.bignum_modinv.bignum_modinv z a b w ⦃ r =>
      r.1.length = z.length ∧
        (Nat.Coprime (wordsNat a.val) (wordsNat b.val) → wordsNat b.val % 2 = 1 → wordsNat b.val ≠ 1 →
          wordsNat r.1.val < wordsNat b.val ∧ wordsNat a.val * wordsNat r.1.val % wordsNat b.val = 1) ⦄

/-! ### RSA

Each routine reads its inputs at the lengths its Rust wrapper asserts, so a
theorem assumes them, and its `&mut` result keeps its length, as Rust's do. -/

/-- `BIGNUM_KMUL_16_32_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_kmul_16_32.ml#L1805 -/
@[step]
axiom bignum_kmul_16_32_spec (z x y : Slice U64) (t : Std.Array U64 32#usize)
    (hz : z.length = 32) (hx : x.length = 16) (hy : y.length = 16) :
    low.x86_64.bignum_kmul_16_32.bignum_kmul_16_32 z x y t ⦃ r =>
      r.1.length = 32 ∧ wordsNat r.1.val = wordsNat x.val * wordsNat y.val ⦄

/-- `BIGNUM_KMUL_32_64_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_kmul_32_64.ml#L3145 -/
@[step]
axiom bignum_kmul_32_64_spec (z x y : Slice U64) (t : Std.Array U64 96#usize)
    (hz : z.length = 64) (hx : x.length = 32) (hy : y.length = 32) :
    low.x86_64.bignum_kmul_32_64.bignum_kmul_32_64 z x y t ⦃ r =>
      r.1.length = 64 ∧ wordsNat r.1.val = wordsNat x.val * wordsNat y.val ⦄

/-- `BIGNUM_KSQR_16_32_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_ksqr_16_32.ml#L1203 -/
@[step]
axiom bignum_ksqr_16_32_spec (z x : Slice U64) (t : Std.Array U64 24#usize)
    (hz : z.length = 32) (hx : x.length = 16) :
    low.x86_64.bignum_ksqr_16_32.bignum_ksqr_16_32 z x t ⦃ r =>
      r.1.length = 32 ∧ wordsNat r.1.val = wordsNat x.val ^ 2 ⦄

/-- `BIGNUM_KSQR_32_64_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_ksqr_32_64.ml#L2065 -/
@[step]
axiom bignum_ksqr_32_64_spec (z x : Slice U64) (t : Std.Array U64 72#usize)
    (hz : z.length = 64) (hx : x.length = 32) :
    low.x86_64.bignum_ksqr_32_64.bignum_ksqr_32_64 z x t ⦃ r =>
      r.1.length = 64 ∧ wordsNat r.1.val = wordsNat x.val ^ 2 ⦄

/-- `BIGNUM_EMONTREDC_8N_SUBROUTINE_CORRECT`, for `m`'s length as `k`, which
returns the carry and leaves the quotient in `z`'s low half and the reduced
value in its high half,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_emontredc_8n.ml#L1937 -/
@[step]
axiom bignum_emontredc_8n_spec (z m : Slice U64) (w : U64) (hz : z.length = 2 * m.length)
    (h8 : m.length % 8 = 0) :
    low.x86_64.bignum_emontredc_8n.bignum_emontredc_8n z m w ⦃ r =>
      r.2.length = z.length ∧
        ((wordsNat m.val * w.val + 1) % 2 ^ 64 = 0 →
          wordsNat m.val * wordsNat (r.2.val.take m.length) + wordsNat z.val =
            2 ^ (64 * m.length) *
              (2 ^ (64 * m.length) * r.1.val + wordsNat (r.2.val.drop m.length))) ⦄

/-- `BIGNUM_OPTSUB_SUBROUTINE_CORRECT`, whose borrow the wrapper drops,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_optsub.ml#L209 -/
@[step]
axiom bignum_optsub_spec (z x y : Slice U64) (p : U64) (hx : x.length = z.length)
    (hy : y.length = z.length) :
    low.x86_64.bignum_optsub.bignum_optsub z x y p ⦃ r =>
      r.length = z.length ∧
        wordsNat r.val =
          if p.val = 0 then wordsNat x.val
          else if wordsNat y.val ≤ wordsNat x.val then wordsNat x.val - wordsNat y.val
          else 2 ^ (64 * z.length) + wordsNat x.val - wordsNat y.val ⦄

/-- `BIGNUM_BITSIZE_SUBROUTINE_CORRECT`, for the slice's length as `k`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_bitsize.ml#L225 -/
@[step]
axiom bignum_bitsize_spec (x : Slice U64) :
    low.x86_64.bignum_bitsize.bignum_bitsize x ⦃ r => r.val = (wordsNat x.val).size ⦄

/-- `BIGNUM_NEGMODINV_SUBROUTINE_CORRECT`,
https://github.com/awslabs/s2n-bignum/blob/b4f17ee743ebc9b53a26c3cd1908f50f0658314f/x86/proofs/bignum_negmodinv.ml#L673 -/
@[step]
axiom bignum_negmodinv_spec (z x : Slice U64) (hx : x.length = z.length) :
    low.x86_64.bignum_negmodinv.bignum_negmodinv z x ⦃ r =>
      r.length = z.length ∧
        (wordsNat x.val % 2 = 1 →
          (wordsNat x.val * wordsNat r.val + 1) % 2 ^ (64 * z.length) = 0) ⦄

/-- rind runs on this CPU: its entry guards' CPU-feature checks pass, and its
BMI2/ADX and AVX2 dispatches read the CPU. None reads an input. -/
def Runs : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ (∃ e, low.entry.Entry.new_public = ok e) ∧
    (∃ t, low.x86_64.cpu.HaveBmi2Adx.check = ok t) ∧ ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t

/-- Ed25519 verification's double scalar multiplication runs one of
s2n-bignum's routines: a CPU without ADX lacks AVX2 too, since with it rind
runs a port of curve25519-dalek's AVX2 backend, which nothing proves. -/
def RunsDouble : Prop :=
  low.x86_64.cpu.HaveBmi2Adx.check = ok none → low.x86_64.cpu.HaveAvx2.check = ok none

@[step]
theorem new_secret_spec (h : Runs) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

@[step]
theorem new_public_spec (h : Runs) : low.entry.Entry.new_public ⦃ _ => True ⦄ := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := h
  simp [he]

/-- The dispatch runs one of the twins, whose contracts agree. -/
@[step]
theorem curve25519_x25519_mux_spec (h : Runs) (res scalar point : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.curve25519_x25519 res scalar point ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) (wordsNat point.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.curve25519_x25519
  rw [ht]
  cases t <;> step*

@[step]
theorem curve25519_x25519base_mux_spec (h : Runs) (res scalar : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.curve25519_x25519base res scalar ⦃ r =>
      wordsNat r.val = rfcx25519 (wordsNat scalar.val) 9 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.curve25519_x25519base
  rw [ht]
  cases t <;> step*

@[step]
theorem edwards25519_decode_mux_spec (h : Runs) (z : Std.Array U64 8#usize)
    (c : Std.Array U8 32#usize) :
    low.x86_64.adx_mux.edwards25519_decode z c ⦃ r =>
      (r.1 = true ↔ edValidEncode (leNat c.val)) ∧
        (edValidEncode (leNat c.val) → pairNat r.2.val = edModEncodePair (edDecode (leNat c.val))) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.edwards25519_decode
  rw [ht]
  cases t <;> step*

@[step]
theorem edwards25519_scalarmulbase_mux_spec (h : Runs) (res : Std.Array U64 8#usize)
    (scalar : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.edwards25519_scalarmulbase res scalar ⦃ r =>
      pairNat r.val = edModEncodePair (edPow edB (wordsNat scalar.val)) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.edwards25519_scalarmulbase
  rw [ht]
  cases t <;> step*

@[step]
theorem edwards25519_scalarmuldouble_mux_spec (h : Runs) (hd : RunsDouble)
    (res : Std.Array U64 8#usize) (scalar : Std.Array U64 4#usize)
    (point : Std.Array U64 8#usize) (bscalar : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.edwards25519_scalarmuldouble res scalar point bscalar ⦃ r =>
      ∀ P, edOnCurve P → edModDecodePair (pairNat point.val) = P →
        pairNat r.val =
          edModEncodePair (edMul (edPow P (wordsNat scalar.val)) (edPow edB (wordsNat bscalar.val))) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.edwards25519_scalarmuldouble
  rw [ht]
  cases t
  · rw [hd ht]
    step*
  · step*

@[step]
theorem bignum_madd_n25519_mux_spec (h : Runs) (z x y c : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.bignum_madd_n25519 z x y c ⦃ r =>
      wordsNat r.val = (wordsNat x.val * wordsNat y.val + wordsNat c.val) % n25519 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_madd_n25519
  rw [ht]
  cases t <;> step*

@[step]
theorem bignum_tomont_p256_mux_spec (h : Runs) (z x : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.bignum_tomont_p256 z x ⦃ r =>
      wordsNat r.val = 2 ^ 256 * wordsNat x.val % p256 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_tomont_p256
  rw [ht]
  cases t <;> step*

@[step]
theorem bignum_demont_p256_mux_spec (h : Runs) (z x : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.bignum_demont_p256 z x ⦃ r =>
      wordsNat x.val < p256 → wordsNat r.val = p256RInv * wordsNat x.val % p256 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_demont_p256
  rw [ht]
  cases t <;> step*

@[step]
theorem bignum_montmul_p256_mux_spec (h : Runs) (z x y : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.bignum_montmul_p256 z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val * wordsNat y.val % p256 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_montmul_p256
  rw [ht]
  cases t <;> step*

@[step]
theorem bignum_montsqr_p256_mux_spec (h : Runs) (z x : Std.Array U64 4#usize) :
    low.x86_64.adx_mux.bignum_montsqr_p256 z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 256 * p256 →
        wordsNat r.val = p256RInv * wordsNat x.val ^ 2 % p256 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_montsqr_p256
  rw [ht]
  cases t <;> step*

@[step]
theorem p256_scalarmul_mux_spec (h : Runs) (res : Std.Array U64 8#usize) (scalar : Std.Array U64 4#usize)
    (point : Std.Array U64 8#usize) :
    low.x86_64.adx_mux.p256_scalarmul res scalar point ⦃ r =>
      ∀ P, p256OnCurve P → p256Affine (pairNat point.val) P →
        p256AffineZ (pairNat r.val) (p256Pow P (wordsNat scalar.val)) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p256_scalarmul
  rw [ht]
  cases t <;> step*

@[step]
theorem p256_montjadd_mux_spec (h : Runs) (p3 p1 p2 : Std.Array U64 12#usize) :
    low.x86_64.adx_mux.p256_montjadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents P2 (tripleNat p2.val) →
        (P1 = P2 → P2 = none) → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p256_montjadd
  rw [ht]
  cases t <;> step*

@[step]
theorem p256_montjdouble_mux_spec (h : Runs) (p3 p1 : Std.Array U64 12#usize) :
    low.x86_64.adx_mux.p256_montjdouble p3 p1 ⦃ r =>
      ∀ P, p256Represents P (tripleNat p1.val) → p256Represents (p256Add P P) (tripleNat r.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p256_montjdouble
  rw [ht]
  cases t <;> step*

@[step]
theorem p256_montjmixadd_mux_spec (h : Runs) (p3 p1 : Std.Array U64 12#usize) (p2 : Std.Array U64 8#usize) :
    low.x86_64.adx_mux.p256_montjmixadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p256Represents P1 (tripleNat p1.val) → p256Represents2 P2 (pairNat p2.val) →
        P1 ≠ P2 → p256Represents (p256Add P1 P2) (tripleNat r.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p256_montjmixadd
  rw [ht]
  cases t <;> step*

set_option exponentiation.threshold 384 in
@[step]
theorem bignum_tomont_p384_mux_spec (h : Runs) (z x : Std.Array U64 6#usize) :
    low.x86_64.adx_mux.bignum_tomont_p384 z x ⦃ r =>
      wordsNat r.val = 2 ^ 384 * wordsNat x.val % p384 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_tomont_p384
  rw [ht]
  cases t <;> step*

@[step]
theorem bignum_demont_p384_mux_spec (h : Runs) (z x : Std.Array U64 6#usize) :
    low.x86_64.adx_mux.bignum_demont_p384 z x ⦃ r =>
      wordsNat x.val < p384 → wordsNat r.val = p384RInv * wordsNat x.val % p384 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_demont_p384
  rw [ht]
  cases t <;> step*

set_option exponentiation.threshold 384 in
@[step]
theorem bignum_montmul_p384_mux_spec (h : Runs) (z x y : Std.Array U64 6#usize) :
    low.x86_64.adx_mux.bignum_montmul_p384 z x y ⦃ r =>
      wordsNat x.val * wordsNat y.val ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val * wordsNat y.val % p384 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_montmul_p384
  rw [ht]
  cases t <;> step*

set_option exponentiation.threshold 384 in
@[step]
theorem bignum_montsqr_p384_mux_spec (h : Runs) (z x : Std.Array U64 6#usize) :
    low.x86_64.adx_mux.bignum_montsqr_p384 z x ⦃ r =>
      wordsNat x.val ^ 2 ≤ 2 ^ 384 * p384 →
        wordsNat r.val = p384RInv * wordsNat x.val ^ 2 % p384 ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.bignum_montsqr_p384
  rw [ht]
  cases t <;> step*

@[step]
theorem p384_montjscalarmul_mux_spec (h : Runs) (res : Std.Array U64 18#usize) (scalar : Std.Array U64 6#usize)
    (point : Std.Array U64 18#usize) :
    low.x86_64.adx_mux.p384_montjscalarmul res scalar point ⦃ r =>
      ∀ P, p384OnCurve P → p384Represents P (tripleNat6 point.val) →
        p384Represents (p384Pow P (wordsNat scalar.val)) (tripleNat6 r.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p384_montjscalarmul
  rw [ht]
  cases t <;> step*

@[step]
theorem p384_montjdouble_mux_spec (h : Runs) (p3 p1 : Std.Array U64 18#usize) :
    low.x86_64.adx_mux.p384_montjdouble p3 p1 ⦃ r =>
      ∀ P, p384Represents P (tripleNat6 p1.val) → p384Represents (p384Add P P) (tripleNat6 r.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p384_montjdouble
  rw [ht]
  cases t <;> step*

@[step]
theorem p384_montjmixadd_mux_spec (h : Runs) (p3 p1 : Std.Array U64 18#usize) (p2 : Std.Array U64 12#usize) :
    low.x86_64.adx_mux.p384_montjmixadd p3 p1 p2 ⦃ r =>
      ∀ P1 P2, p384Represents P1 (tripleNat6 p1.val) → p384Represents2 P2 (pairNat6 p2.val) →
        P1 ≠ P2 → p384Represents (p384Add P1 P2) (tripleNat6 r.val) ⦄ := by
  obtain ⟨-, -, ⟨t, ht⟩, -⟩ := h
  unfold low.x86_64.adx_mux.p384_montjmixadd
  rw [ht]
  cases t <;> step*

end rind.x86_64
