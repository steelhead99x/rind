import Rind.P384Group
import Rind.VgNist
import Rind.VgOutcome
import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Spec.Ecdsa.Verify.P384
open Aeneas Aeneas.Std rind.spec VG.Spec.Weierstrass

/-!
# pyca/verified-garbage's P-384 is rind's

VG's P-384 (`VG.Spec.P384.curve`) is rind's (`Rind/Spec.lean`), so
`Rind/VgNist.lean`'s proofs that VG's points, keys, and ECDSA verification
are rind's hold of it.
-/

set_option exponentiation.threshold 400

namespace rind.spec.vgP384

open vgNist

/-- VG's P-384. -/
abbrev C : Curve := VG.Spec.P384.curve

theorem nBits_eq : VG.Spec.Ecdsa.nBits C = 384 := by
  unfold VG.Spec.Ecdsa.nBits
  rw [Nat.log2_eq_iff (by simp [C, VG.Spec.P384.curve, VG.Spec.P384.n]) |>.mpr]
  simp only [C, VG.Spec.P384.curve, VG.Spec.P384.n]
  constructor <;> norm_num

/-- VG's P-384 is rind's. -/
theorem curve_matches : Matches C p384 n384 b384 p384G where
  p_eq := by show VG.Spec.P384.p = p384; decide +kernel
  n_eq := by simp only [C, VG.Spec.P384.curve, VG.Spec.P384.n, n384]
  a_eq := by show VG.Spec.P384.p - 3 = p384 - 3; decide +kernel
  b_eq := rfl
  g_eq := by simp only [G, ofVg, C, VG.Spec.P384.curve, p384G]; rfl
  g_on := p384OnCurve_G
  b_ne := b384_ne_two
  p_le := by simp only [C, VG.Spec.P384.curve, p384]; decide
  hash_bits := by rw [nBits_eq]; decide
  g_mult := p384_g_mult

end rind.spec.vgP384
