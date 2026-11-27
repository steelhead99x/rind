import Rind.P256Multiples
import Rind.VgNist
import Rind.VgOutcome
import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Spec.Ecdh
import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Spec.P256
open Aeneas Aeneas.Std rind.spec VG.Spec.Weierstrass

/-!
# pyca/verified-garbage's P-256 is rind's

VG's P-256 (`VG.Spec.P256.curve`) is rind's (`Rind/Spec.lean`), so
`Rind/VgNist.lean`'s proofs that VG's points, keys, and ECDSA verification
are rind's hold of it; and its ECDH, which only P-256 takes from VG, is
`p256Pow`'s x-coordinate.
-/

namespace rind.spec.vgP256

open vgNist

/-- VG's P-256. -/
abbrev C : Curve := VG.Spec.P256.curve

theorem nBits_eq : VG.Spec.Ecdsa.nBits C = 256 := by
  unfold VG.Spec.Ecdsa.nBits
  rw [Nat.log2_eq_iff (by simp [C, VG.Spec.P256.curve, VG.Spec.P256.n]) |>.mpr]
  simp only [C, VG.Spec.P256.curve, VG.Spec.P256.n]
  constructor <;> norm_num

/-- VG's P-256 is rind's. -/
theorem curve_matches : Matches C p256 n256 b256 p256G where
  p_eq := by simp only [C, VG.Spec.P256.curve, VG.Spec.P256.p, p256]
  n_eq := by simp only [C, VG.Spec.P256.curve, VG.Spec.P256.n, n256]
  a_eq := by simp only [C, VG.Spec.P256.curve, VG.Spec.P256.p, p256]
  b_eq := rfl
  g_eq := by simp only [G, ofVg, C, VG.Spec.P256.curve, p256G]; rfl
  g_on := p256OnCurve_G
  b_ne := b256_ne_two
  p_le := by simp only [C, VG.Spec.P256.curve, p256]; decide
  hash_bits := by rw [nBits_eq]; decide
  g_mult := g_mult

/-- VG's ECDH with an encoded point on the curve, for a scalar in [1, n). -/
theorem exchange_eq (d : Nat) (hd : d < n256) (b : List U8) (hl : b.length = 65)
    (h4 : b.head? = some 4#u8) (hc : p256OnCurve (some (coords C b))) :
    VG.Spec.Ecdh.exchange C d (b.map (·.bv)) =
      match p256Pow (some (coords C b)) d with
      | some (x, _) => some (toBytes 32 x)
      | none => none := by
  have hdec := decode_bv curve_matches b hl h4
  unfold VG.Spec.Ecdh.exchange
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp [p256Pow, nist.pow]
  rw [if_pos ⟨hd0, curve_matches.n_eq ▸ hd⟩]
  rcases hQ : VG.Spec.EcKey.decodePublicKey C (b.map (·.bv)) with _ | Q
  · rw [hQ] at hdec; exact absurd hc hdec
  · rw [hQ] at hdec
    obtain ⟨hon, hQ'⟩ := hdec
    have hm := ofVg_mul_pow curve_matches (hQ' ▸ hon : p256OnCurve (ofVg Q)) d
    rw [hQ'] at hm
    rw [show p256Pow = nist.pow p256 from rfl, ← hm, hQ]
    dsimp only
    rcases mul d Q with _ | ⟨x, y⟩ <;> rfl

end rind.spec.vgP256
