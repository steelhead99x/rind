import Rind.Ed25519
import VerifiedGarbage.Spec.Ed25519
open Aeneas Aeneas.Std

/-!
# pyca/verified-garbage's X25519 and Ed25519, as rind's proofs read them

What `Rind.X86_64.VgCurve25519`'s axioms and the proofs over them share:
bytes as VG's specs take them, `bvs`, and RFC 7748's X25519 as VG's spec,
`VG.Spec.X25519.x25519`, states it, read as a function of numbers the way
`Rind.Spec`'s `rfcx25519` is, `vgX25519`. Its byte encodings are VG's own
RFC 8032 ones, `VG.Spec.Ed25519.encodeLE` and `VG.Spec.Ed25519.decodeLE`,
which `Rind.Spec`'s `leNat` agrees with.
-/

namespace rind.spec

/-- Bytes as VG's specs take them. -/
def bvs (l : List U8) : List VG.Byte := l.map (·.bv)

theorem length_bvs (l : List U8) : (bvs l).length = l.length := by simp [bvs]

theorem bvs_inj (a b : List U8) : bvs a = bvs b ↔ a = b := by
  refine ⟨fun h => List.map_injective_iff.mpr (fun x y hxy => ?_) h, fun h => h ▸ rfl⟩
  cases x; cases y; simp_all

/-- RFC 7748's X25519 as VG's spec states it, of a scalar and a u-coordinate
each read as a number: their 32 little-endian bytes in, and the result's out. -/
def vgX25519 (k u : Nat) : Nat :=
  VG.Spec.Ed25519.decodeLE (VG.Spec.X25519.x25519 (VG.Spec.Ed25519.encodeLE 32 k) (VG.Spec.Ed25519.encodeLE 32 u))

theorem decodeLE_bvs (l : List U8) : VG.Spec.Ed25519.decodeLE (bvs l) = leNat l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [bvs, List.map_cons] at ih ⊢
    simp [VG.Spec.Ed25519.decodeLE, ih, leNat, Nat.ofDigits_cons]

theorem encodeLE_succ (n x : Nat) :
    VG.Spec.Ed25519.encodeLE (n + 1) x = BitVec.ofNat 8 x :: VG.Spec.Ed25519.encodeLE n (x / 256) := by
  simp only [VG.Spec.Ed25519.encodeLE, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, Nat.succ_eq_add_one, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  congr 2
  rw [show 8 * (i + 1) = 8 + 8 * i by ring, pow_add]
  norm_num

/-- Encoding then decoding `n` bytes keeps `x` mod 256ⁿ. -/
theorem decodeLE_encodeLE (n x : Nat) :
    VG.Spec.Ed25519.decodeLE (VG.Spec.Ed25519.encodeLE n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [VG.Spec.Ed25519.encodeLE, VG.Spec.Ed25519.decodeLE, Nat.mod_one]
  | succ n ih =>
    rw [encodeLE_succ, VG.Spec.Ed25519.decodeLE, ih, BitVec.toNat_ofNat,
      show (2 : Nat) ^ 8 = 256 from rfl, pow_succ', Nat.mod_mul]

/-- VG's encoding of `n` bytes is `leBytesOf`'s, as VG's specs take bytes. -/
theorem encodeLE_eq (n x : Nat) : VG.Spec.Ed25519.encodeLE n x = bvs (leBytesOf n x) := by
  simp only [VG.Spec.Ed25519.encodeLE, bvs, leBytesOf, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp [Nat.shiftRight_eq_div_pow, pow_mul]

/-- The base point's u-coordinate, 9, as VG's spec encodes it. -/
theorem encodeLE_nine : VG.Spec.Ed25519.encodeLE 32 9 = VG.Spec.X25519.basePoint := by decide

end rind.spec
