import Rind.X86_64.P256Ecdsa
open Aeneas Aeneas.Std Result rind.spec

/-!
# x86_64's check that a signing key's public key is an encoding

What the shared `Rind.X86_64.P256Signature` takes of each target's
`SigningKey::is_public_key`: `is_public_key_of`, that it returns what SEC 1's
comparison with the key's own encoding does, or, for an X9.62 uncompressed
encoding, whether it encodes the key's scalar times G. x86_64 checks an
uncompressed encoding without encoding its own: it parses the point and
compares it with the generator multiplication's Jacobian result,
`P256Base.jac_base_multiply_spec`, scaled by that result's z, and stores the
encoding it checked as the key's.
-/

namespace rind.x86_64

namespace P256

/-- The parsed point's Montgomery coordinates `a` and `e`, scaled by z² and
z³, equal the Jacobian X and Y exactly when the point is the one they name. -/
theorem jacobian_matches (X Y Z a e : Nat) (P : Nat × Nat) (hX : X < p256) (hY : Y < p256)
    (hP : p256OfJacobian (p256RInv * X % p256) (p256RInv * Y % p256) (p256RInv * Z % p256) = some P) :
    (decide (p256RInv * a * (p256RInv * Z ^ 2 % p256) % p256 = X) &&
      decide (p256RInv * e * (p256RInv * (p256RInv * Z ^ 2 % p256) * Z % p256) % p256 = Y)) = true ↔
      P = (p256RInv * a % p256, p256RInv * e % p256) := by
  rw [ofJacobian_dec] at hP
  split_ifs at hP with hz0
  obtain rfl := Option.some.inj hP
  have hlt : ∀ n, n % p256 < p256 := fun n => Nat.mod_lt _ p256_pos
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [eq_of_dec _ _ (hlt _) hX, eq_of_dec _ _ (hlt _) hY, dec_mont_mul, dec_mont_sqr, dec_mont_mul,
    dec_mont_mul, dec_mont_sqr, val_dec a, val_dec e, Prod.mk.injEq]
  have hz3 : dec Z ^ 2 * dec Z = dec Z ^ 3 := by ring
  rw [hz3]
  have h2 : dec Z ^ 2 ≠ 0 := pow_ne_zero _ hz0
  have h3 : dec Z ^ 3 ≠ 0 := pow_ne_zero _ hz0
  constructor
  · rintro ⟨hx, hy⟩
    rw [← hx, ← hy, mul_inv_cancel_right₀ h2, mul_inv_cancel_right₀ h3]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hx, hy⟩
    rw [← ZMod.val_injective _ hx, ← ZMod.val_injective _ hy, inv_mul_cancel_right₀ h2,
      inv_mul_cancel_right₀ h3]
    exact ⟨rfl, rfl⟩

/-- `StaticPrivateKey::public_key_is_uncompressed`, for a scalar in [1, n)
and an encoding tagged uncompressed: whether it encodes the scalar times G. -/
theorem public_key_is_uncompressed_spec (h : Runs) (k : mid.p256.StaticPrivateKey)
    (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n256) (enc : Slice U8)
    (h4 : enc.val.head? = some 4#u8) :
    mid.p256.StaticPrivateKey.public_key_is_uncompressed k enc ⦃ b =>
      b = true ↔ enc.length = 65 ∧ p256Pow p256G (scNat k.scalar) = some (x962Coords enc.val) ⦄ := by
  obtain ⟨x, y, hq, hc⟩ := g_mult _ hk0 hk
  unfold mid.p256.StaticPrivateKey.public_key_is_uncompressed low.ct.into_public
  rw [hq]
  step with new_secret_spec h
  step with public_from_x962_spec h enc as ⟨r, hr⟩
  rw [h4] at hr
  simp only [↓reduceIte] at hr
  by_cases hl : enc.length = 65
  swap
  · simp only [hl, ↓reduceIte] at hr
    subst hr
    simp only [WP.spec_ok]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨h, _⟩ => absurd h hl⟩
  simp only [hl, ↓reduceIte] at hr
  by_cases hon : p256OnCurve (some (x962Coords enc.val))
  swap
  · simp only [hon, ↓reduceIte] at hr
    subst hr
    simp only [WP.spec_ok]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, heq⟩ => absurd (heq ▸ hc) hon⟩
  simp only [hon, ↓reduceIte] at hr
  obtain ⟨pk, rfl, hpk⟩ := hr
  simp only
  have hl8 : pk.point.xy.val.length = 8 := pk.point.xy.property
  step with P256Base.jac_base_multiply_spec (P256Base.runsSelect_of_runs h) k.scalar hk as ⟨prod, hprod⟩
  rw [hq] at hprod
  obtain ⟨hX, hY, hZ, hP⟩ := hprod
  step with jac_z_spec prod as ⟨fz, hfz⟩
  have hfzv : feNat fz = (tripleNat prod.xyz.val).2.2 := by simp [feNat, hfz, tripleNat]
  step with mont_sqr_spec h fz (by rw [hfzv]; exact hZ) as ⟨z2, hz2⟩
  step with mont_mul_spec h z2 fz (fe_lt_p256 _ _ hz2) (by rw [hfzv]; exact hZ) as ⟨z3, hz3⟩
  step with point_x_spec pk.point as ⟨fe1, hfe1⟩
  have hfe1v : feNat fe1 = (pairNat pk.point.xy.val).1 := by simp [feNat, hfe1, pairNat]
  step with mont_mul_spec h fe1 z2 (by rw [hfe1v]; exact hpk.1) (fe_lt_p256 _ _ hz2) as ⟨xm, hxm⟩
  step with point_y_spec pk.point as ⟨fe2, hfe2⟩
  have hfe2v : feNat fe2 = (pairNat pk.point.xy.val).2 := by
    rw [pairNat_drop _ hl8]; simp [feNat, hfe2]
  step with mont_mul_spec h fe2 z3 (by rw [hfe2v]; exact hpk.2.1) (fe_lt_p256 _ _ hz3) as ⟨ym, hym⟩
  simp only [lift, bind_ok]
  step with jac_x_spec prod as ⟨fx, hfx⟩
  have hfxv : feNat fx = (tripleNat prod.xyz.val).1 := by simp [feNat, hfx, tripleNat]
  step as ⟨b, hb⟩
  step with jac_y_spec prod as ⟨fy, hfy⟩
  have hfyv : feNat fy = (tripleNat prod.xyz.val).2.1 := by simp [feNat, hfy, tripleNat]
  step as ⟨b1, hb1⟩
  have hbv : b = decide (feNat xm = feNat fx) := by rw [hb]; simp [feNat]
  have hb1v : b1 = decide (feNat ym = feNat fy) := by rw [hb1]; simp [feNat]
  rw [hbv, hb1v, hxm, hym, hz3, hz2, hfe1v, hfe2v, hfzv, hfxv, hfyv,
    jacobian_matches _ _ _ _ _ (x, y) hX hY hP, ← hpk.2.2]
  simp [hl]

/-- The build `is_public_key` stores a checked encoding with: a copy of it,
which returns for an encoding that fits. -/
theorem key_check_build_spec (enc : Slice U8) (hl : enc.length = 65) :
    high.ecdsa.SigningKey.is_public_key.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
      P256C enc () ⦃ _ => True ⦄ := by
  unfold high.ecdsa.SigningKey.is_public_key.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
    high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault.default
  step*

theorem is_public_key_of (h : Runs) (hc : Cached) (key : P256SigningKey) (enc : Slice U8)
    (hk0 : 0 < scNat key.private_key.scalar) (hk : scNat key.private_key.scalar < n256) (Post : Bool → Prop)
    (hsec1 : (do
      let ep ← high.ecdsa.SigningKey.public_key_uncompressed P256C key
      let s ← high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref ep
      high.sec1.is_public_key s enc) ⦃ Post ⦄)
    (hfast : ∀ m : Bool, enc.val.head? = some 4#u8 →
      (m = true ↔ enc.length = 65 ∧
        p256Pow p256G (scNat key.private_key.scalar) = some (x962Coords enc.val)) → Post m) :
    high.ecdsa.SigningKey.is_public_key P256C key enc ⦃ Post ⦄ := by
  unfold high.ecdsa.SigningKey.is_public_key
  step as ⟨e, he⟩
  split
  · exact hsec1
  have hne : enc.val ≠ [] := by
    intro h0; simp [Slice.length, h0] at he; contradiction
  obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
  step as ⟨i, hi⟩
  split
  swap
  · exact hsec1
  rename_i hi4
  have h4 : enc.val.head? = some 4#u8 := by
    rw [hct, List.head?_cons, ← hi4, hi]; simp [hct]
  simp only [mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.public_key_is_uncompressed]
  step with public_key_is_uncompressed_spec h key.private_key hk0 hk enc h4 as ⟨m, hm⟩
  cases m
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact hfast false h4 hm
  · simp only [↓reduceIte]
    step with hc.point_get_or_build_now_any
      (high.ecdsa.SigningKey.is_public_key.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint P256C) key enc (key_check_build_spec enc (hm.mp rfl).1)
    exact hfast true h4 hm

end P256

end rind.x86_64
