import Rind.Spec
import ForHumans.Specs.X25519
import ForHumans.Specs.Representation.Array
open Aeneas Aeneas.Std

/-!
# Beneficial AI Foundation's curve25519-dalek specs, as rind's proofs read them

What each target's restatement of Beneficial AI Foundation's (BAIF's)
curve25519-dalek theorems and the proofs over it share: RFC 7748's X25519 as
BAIF's spec, `curve25519.X25519`, states it, read as a function of numbers the
way `Rind.Spec`'s `rfcx25519` is, `dalekX25519`. Its byte encodings are BAIF's
own, `curve25519.decodeLittleEndian` and `curve25519.encodeLittleEndian`, which
`Rind.Spec`'s `leNat` agrees with.
-/

namespace rind.spec

/-- RFC 7748's X25519 as BAIF's spec states it, of a scalar and a u-coordinate
each read as a number: their 32 little-endian bytes in, and the result's out. -/
def dalekX25519 (k u : Nat) : Nat :=
  curve25519.decodeLittleEndian
    (curve25519.X25519 (curve25519.encodeLittleEndian 32 k) (curve25519.encodeLittleEndian 32 u))

/-- BAIF's reading of a byte array is `leNat`'s. -/
theorem decodeLittleEndian_toVector {n : Usize} (a : Std.Array U8 n) :
    curve25519.decodeLittleEndian a.toVector = leNat a.val := by
  simp only [curve25519.decodeLittleEndian, Std.Array.toVector, leNat, Vector.toList_mk, List.map_map]
  congr 1

theorem encodeLittleEndian_succ (n x : Nat) :
    (curve25519.encodeLittleEndian (n + 1) x).toList =
      UInt8.ofNat x :: (curve25519.encodeLittleEndian n (x / 256)).toList := by
  simp only [curve25519.encodeLittleEndian, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero,
    pow_zero, Nat.div_one, Fin.val_succ]
  congr 2
  funext i
  rw [Nat.div_div_eq_div_mul, pow_succ']

/-- BAIF's encoding of a byte list's number, in as many bytes, is the list. -/
theorem encodeLittleEndian_leNat (l : List U8) :
    (curve25519.encodeLittleEndian l.length (leNat l)).toList = l.map fun x => UInt8.ofBitVec x.bv := by
  induction l with
  | nil => simp [curve25519.encodeLittleEndian]
  | cons b l ih =>
    have hb : b.val < 256 := b.hBounds
    have hl : leNat (b :: l) = b.val + 256 * leNat l := by
      simp [leNat, Nat.ofDigits_cons]
    rw [List.length_cons, encodeLittleEndian_succ, hl,
      show (b.val + 256 * leNat l) / 256 = leNat l by omega, ih, List.map_cons]
    congr 1
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofBitVec, UScalar.bv_toNat]
    omega

/-- BAIF's 32-byte encoding of an array's number is the array. -/
theorem encodeLittleEndian_leNat_array (a : Std.Array U8 32#usize) :
    curve25519.encodeLittleEndian 32 (leNat a.val) = a.toVector := by
  have h : ∀ n, a.val.length = n →
      (curve25519.encodeLittleEndian n (leNat a.val)).toList = a.val.map fun x => UInt8.ofBitVec x.bv := by
    rintro n rfl
    exact encodeLittleEndian_leNat a.val
  apply Vector.toList_inj.mp
  rw [h 32 a.property]
  simp [Std.Array.toVector]

/-- The base point's u-coordinate, 9, as BAIF's spec encodes it. -/
theorem encodeUCoordinate_nine : curve25519.encodeUCoordinate 9 = curve25519.encodeLittleEndian 32 9 := by
  simp only [curve25519.encodeUCoordinate, curve25519.encodeU]
  congr 1

/-- An X25519 whose bytes BAIF's spec states is `dalekX25519` of their numbers. -/
theorem dalekX25519_eq (k u r : Std.Array U8 32#usize)
    (h : r.toVector = curve25519.X25519 k.toVector u.toVector) :
    leNat r.val = dalekX25519 (leNat k.val) (leNat u.val) := by
  rw [← decodeLittleEndian_toVector, h, dalekX25519, encodeLittleEndian_leNat_array k,
    encodeLittleEndian_leNat_array u]

/-- An X25519 of the base point whose bytes BAIF's spec states is
`dalekX25519` of the scalar's number and 9. -/
theorem dalekX25519_base_eq (k r : Std.Array U8 32#usize)
    (h : r.toVector = curve25519.X25519 k.toVector (curve25519.encodeUCoordinate 9)) :
    leNat r.val = dalekX25519 (leNat k.val) 9 := by
  rw [← decodeLittleEndian_toVector, h, dalekX25519, encodeLittleEndian_leNat_array k,
    encodeUCoordinate_nine]

end rind.spec
