import Rind.Aarch64.P256Agree
import Rind.Aarch64.P256Table
open Aeneas Aeneas.Std Result rind.spec

/-!
# aarch64's P-256 generator multiplication

What the shared key generation and ECDSA proofs, `Rind.Aarch64.P256` and
those above it, take of each target's generator multiplication and table:
`base_multiply_spec`, the generator times a scalar below n, and `first_row`,
that the table's first row holds G to 32G. aarch64 multiplies by s2n-bignum's
`p256_scalarmulbase` over the table `Rind.Aarch64.P256Table` checks, which
holds every multiple that routine's proof assumes, for any scalar.
-/

namespace rind.aarch64

namespace P256

@[step]
theorem base_multiply_spec (_hr : Runs) (k : mid.p256.Scalar) (_hk : wordsNat k.val < n256) :
    mid.p256.AffineMontPoint.base_multiply k ⦃ q =>
      ∃ rx ry, p256AffineZ (rx, ry) (p256Pow p256G (wordsNat k.val)) ∧
        pairNat q.xy.val = (2 ^ 256 * rx % p256, 2 ^ 256 * ry % p256) ⦄ := by
  unfold mid.p256.AffineMontPoint.base_multiply
  step*
  · simp [mid.p256.AffineMontPoint.X]
  · simp [mid.p256.AffineMontPoint.X]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.AffineMontPoint.X]) r_post
  · simp [mid.p256.AffineMontPoint.Y]
  · simp [mid.p256.AffineMontPoint.Y]
  · rcases r1 with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s1_post1, mid.p256.AffineMontPoint.Y]) r1_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    subst r1_post
    obtain ⟨ha1, -⟩ := r1_post
    have h8 : (xy1.val).length = 8 := xy1.property
    have hxa : feNat a = (pairNat xy1.val).1 := by
      simp [feNat, ha, s_post, mid.p256.AffineMontPoint.X, List.slice, pairNat]
    have hya : feNat a1 = (pairNat xy1.val).2 := by
      rw [pairNat_drop _ h8]
      simp [feNat, ha1, s1_post, mid.p256.AffineMontPoint.Y, List.slice, List.take_of_length_le, h8]
    refine ⟨(pairNat xy1.val).1, (pairNat xy1.val).2, xy1_post _ p256OnCurve_G tabulated, ?_⟩
    rw [q_post, pairNat_append _ _ fe.property fe1.property, ← hxa, ← hya]
    exact Prod.ext fe_post fe1_post

/-- The generator table's first row holds G to 32G, which `tabulated` states
of every row's multiples. -/
theorem first_row : ∀ j, 1 ≤ j → j ≤ 32 →
    p256Represents2 (p256Pow p256G j) (pairNat ((mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[0]!).val.drop (8 * (j - 1)))) :=
  fun j hj1 hj => by simpa using tabulated 0 (by norm_num) j hj1 hj

end P256

end rind.aarch64
