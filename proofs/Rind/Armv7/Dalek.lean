import Rind.Armv7.Funs
import Rind.Dalek
import ForHumans.Specs.Edwards
open Aeneas Aeneas.Std Result rind.spec

/-!
# Beneficial AI Foundation's curve25519-dalek on armv7

On armv7 rind runs curve25519-dalek's serial 32-bit backend, with its
precomputed tables, for X25519's public key on every CPU and for its shared
secret on a CPU without NEON (`Rind.Armv7.Curve25519`), and for Ed25519
(`Rind.Armv7.Ed25519`). Beneficial AI Foundation (BAIF) proves that backend
in Lean, through Aeneas, in its fork of the crate. Each axiom here restates
one of BAIF's theorems, at the revision `admin/import-dalek` pins (f6351dfe),
about a dalek function rind calls, which the armv7 translation leaves opaque,
in BAIF's specs of X25519, `curve25519.X25519`, and of edwards25519, its
group of points `curve25519.edwards.Point` with RFC 8032's encoding, which
`admin/import-dalek` vendors into `proofs/curve25519-dalek` byte for byte with
the modules they import. An array of bytes is the vector of them BAIF's
`Array.toVector` reads, and a scalar the number its bytes encode, as in BAIF's
statements.

The translation leaves dalek's `EdwardsPoint` opaque, since rind only passes
one between dalek's functions, so BAIF's reading of one, `toPoint`, and the
invariant its theorems take and keep, `OnCurve` and `IsBounded`, which name
its fields, are opaque here too: `EdwardsPoint.toPoint` and
`EdwardsPoint.Valid`. Each axiom states them where BAIF's theorem states
BAIF's.

BAIF's theorems are about its translation of its fork's source, by the Aeneas
release its `AENEAS_VERSION.txt` names, with dalek's `alloc` and `zeroize`
features, which rind's build turns on too. `admin/prove dalek` translates the
crates.io release rind builds the same way and fails unless every definition
these functions reach in the configuration armv7 builds, 32-bit with
precomputed tables, is BAIF's.

Trusted: each restatement, with `EdwardsPoint.toPoint` and
`EdwardsPoint.Valid` standing for BAIF's definitions, BAIF's proofs, which rest on Lean's axioms and
BAIF's own about the `alloc`, `subtle`, and `zeroize` functions dalek calls,
and Aeneas's translation of the Rust, as everywhere here.
-/

namespace rind.armv7

/-- `MontgomeryPoint::mul_clamped`: RFC 7748's `X25519(bytes, P)`,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Montgomery.lean#L71
(`Theorems.montgomery.MontgomeryPoint.mul_clamped`). -/
@[step]
axiom dalek_mul_clamped_spec (P : curve25519_dalek.montgomery.MontgomeryPoint)
    (bytes : Std.Array U8 32#usize) :
    curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped P bytes ⦃ r =>
      r.toVector = curve25519.X25519 bytes.toVector P.toVector ⦄

/-- `MontgomeryPoint::mul_base_clamped`: RFC 7748's `X25519(bytes, 9)`,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Montgomery.lean#L78
(`Theorems.montgomery.MontgomeryPoint.mul_base_clamped`). -/
@[step]
axiom dalek_mul_base_clamped_spec (bytes : Std.Array U8 32#usize) :
    curve25519_dalek.montgomery.MontgomeryPoint.mul_base_clamped bytes ⦃ r =>
      r.toVector = curve25519.X25519 bytes.toVector (curve25519.encodeUCoordinate 9) ⦄

/-! ## Ed25519 -/

/-- The point of edwards25519 a dalek point represents: BAIF's
`EdwardsPoint.toPoint`, its extended coordinates' affine point. -/
noncomputable opaque curve25519_dalek.edwards.EdwardsPoint.toPoint :
    curve25519_dalek.edwards.EdwardsPoint → curve25519.edwards.Point := fun _ => 0

/-- What BAIF's theorems take of a dalek point and keep: `OnCurve`, its
coordinates on the curve, and `IsBounded`, its limbs within the bounds
dalek's arithmetic needs. -/
opaque curve25519_dalek.edwards.EdwardsPoint.Valid : curve25519_dalek.edwards.EdwardsPoint → Prop

/-- `CompressedEdwardsY::decompress`: the lenient decoding of the bytes, `y`
reduced mod p and a set sign bit on `x = 0` taken as `x = 0`,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Edwards/Bits32Tables.lean#L36
(`Theorems.edwards.«32bit-tables».CompressedEdwardsY.decompress`). -/
@[step]
axiom dalek_decompress_spec (c : curve25519_dalek.edwards.CompressedEdwardsY) :
    curve25519_dalek.edwards.CompressedEdwardsY.decompress c ⦃ r =>
      r.map (·.toPoint) = curve25519.decodeLenient c.toVector ∧ ∀ P, r = some P → P.Valid ⦄

/-- `EdwardsPoint::compress`: RFC 8032's encoding of the point,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Edwards/Bits32Tables.lean#L133
(`Theorems.edwards.«32bit-tables».EdwardsPoint.compress`). -/
@[step]
axiom dalek_compress_spec (P : curve25519_dalek.edwards.EdwardsPoint) (hP : P.Valid) :
    curve25519_dalek.edwards.EdwardsPoint.compress P ⦃ r =>
      r.toVector = curve25519.encode P.toPoint ⦄

/-- `Neg for EdwardsPoint`: the point's negation,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Edwards/Bits32Tables.lean#L263
(`Theorems.edwards.«32bit-tables».EdwardsPoint.neg`, its `-P`). -/
@[step]
axiom dalek_neg_spec (P : curve25519_dalek.edwards.EdwardsPoint) (hP : P.Valid) :
    curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg P ⦃ r =>
      r.Valid ∧ r.toPoint = -P.toPoint ⦄

/-- `EdwardsPoint::mul_base`: the base point times a scalar below 2²⁵⁵,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Edwards/Bits32Tables.lean#L290
(`Theorems.edwards.«32bit-tables».EdwardsPoint.mul_base`). -/
@[step]
axiom dalek_mul_base_spec (s : curve25519_dalek.scalar.Scalar) (hs : s.bytes.asNat 8 < 2 ^ 255) :
    curve25519_dalek.edwards.EdwardsPoint.mul_base s ⦃ r =>
      r.Valid ∧ r.toPoint = s.bytes.asNat 8 • curve25519.basepoint ⦄

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `aA + bB`, for
scalars below 2²⁵⁵ and the base point `B`,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Edwards/Bits32Tables.lean#L444
(`Theorems.edwards.«32bit-tables».EdwardsPoint.vartime_double_scalar_mul_basepoint`). -/
@[step]
axiom dalek_vartime_double_scalar_mul_basepoint_spec (a : curve25519_dalek.scalar.Scalar)
    (A : curve25519_dalek.edwards.EdwardsPoint) (b : curve25519_dalek.scalar.Scalar)
    (ha : a.bytes.asNat 8 < 2 ^ 255) (hA : A.Valid) (hb : b.bytes.asNat 8 < 2 ^ 255) :
    curve25519_dalek.edwards.EdwardsPoint.vartime_double_scalar_mul_basepoint a A b ⦃ r =>
      r.Valid ∧ r.toPoint = a.bytes.asNat 8 • A.toPoint + b.bytes.asNat 8 • curve25519.basepoint ⦄

/-- `Scalar::from_bytes_mod_order`: the 32 bytes' number mod L,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Scalar.lean#L18
(`Theorems.scalar.Scalar.from_bytes_mod_order`). -/
@[step]
axiom dalek_from_bytes_mod_order_spec (bytes : Std.Array U8 32#usize) :
    curve25519_dalek.scalar.Scalar.from_bytes_mod_order bytes ⦃ r =>
      r.bytes.asNat 8 = bytes.asNat 8 % curve25519.L ⦄

/-- `Scalar::from_bytes_mod_order_wide`: the 64 bytes' number mod L,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Scalar.lean#L24
(`Theorems.scalar.Scalar.from_bytes_mod_order_wide`). -/
@[step]
axiom dalek_from_bytes_mod_order_wide_spec (input : Std.Array U8 64#usize) :
    curve25519_dalek.scalar.Scalar.from_bytes_mod_order_wide input ⦃ r =>
      r.bytes.asNat 8 = input.asNat 8 % curve25519.L ⦄

/-- `Scalar::from_canonical_bytes`: the bytes, and whether their number is
below L,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Scalar.lean#L30
(`Theorems.scalar.Scalar.from_canonical_bytes`). -/
@[step]
axiom dalek_from_canonical_bytes_spec (bytes : Std.Array U8 32#usize) :
    curve25519_dalek.scalar.Scalar.from_canonical_bytes bytes ⦃ r =>
      r.value.bytes = bytes ∧ (bytes.asNat 8 < curve25519.L → r.is_some = 1#u8) ∧
        (curve25519.L ≤ bytes.asNat 8 → r.is_some = 0#u8) ⦄

/-- `Mul for Scalar`: the product mod L,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Scalar.lean#L55
(`Theorems.scalar.Scalar.mul`, its `a * b`). -/
@[step]
axiom dalek_scalar_mul_spec (a b : curve25519_dalek.scalar.Scalar) :
    curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar.mul a b ⦃ r =>
      r.bytes.asNat 8 = a.bytes.asNat 8 * b.bytes.asNat 8 % curve25519.L ⦄

/-- `Add for Scalar`: the sum mod L, of scalars below L,
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/blob/f6351dfe59cdd894f94260bc66de33d6bff8e6f6/curve25519-dalek/lean/ForHumans/Theorems/Scalar.lean#L68
(`Theorems.scalar.Scalar.add`, its `a + b`). -/
@[step]
axiom dalek_scalar_add_spec (a b : curve25519_dalek.scalar.Scalar) (ha : a.bytes.asNat 8 < curve25519.L)
    (hb : b.bytes.asNat 8 < curve25519.L) :
    curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar.add a b ⦃ r =>
      r.bytes.asNat 8 = (a.bytes.asNat 8 + b.bytes.asNat 8) % curve25519.L ⦄

end rind.armv7
