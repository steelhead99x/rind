import Rind.X86_64.P256
import Rind.X86_64.EcdsaDispatch
import Rind.P256Multiples
open Aeneas Aeneas.Std Result rind.spec

/-!
# P-256 ECDSA, proven from rind's signature API to s2n-bignum's contracts

The twin multiplication of verification looks the generator's multiples up in
the generator table's first row, as `Rind.X86_64.P256Base` states it holds
them. `admin/prove` writes the aarch64 proof from this file by renaming the
target.
-/

namespace rind.x86_64

namespace P256

/-! ## Scalars mod n, `mid::p256::Scalar` -/

/-- HOL Light's `inverse_mod n_256 (2 EXP 256)`. -/
def n256RInv : Nat :=
  43790243014242295660885426880012836369732278457577312309071968676491870960761

theorem n256RInv_spec : 2 ^ 256 * n256RInv % n256 = 1 % n256 := by
  simp only [n256RInv, n256]; decide

theorem n256_lt : n256 < 2 ^ 256 := by unfold n256; decide

theorem n256_odd : n256 % 2 = 1 := by unfold n256; decide

theorem CURVE_ORDER_val : wordsNat mid.p256.CURVE_ORDER.val = n256 := by
  simp only [mid.p256.CURVE_ORDER, Array.make, wordsNat, n256]; decide

/-- `CURVE_ORDER_MM`, 2⁵¹² mod n, the Montgomery form of 2²⁵⁶. -/
def n256MM : Nat := 46533765739406314298121036767150998762426774378559716911348521029833835802274

theorem n256MM_spec : n256MM < n256 ∧ n256RInv * n256MM % n256 = 2 ^ 256 % n256 := by
  unfold n256MM n256RInv n256; decide

theorem CURVE_ORDER_MM_val : wordsNat mid.p256.CURVE_ORDER_MM.val = n256MM := by
  simp only [mid.p256.CURVE_ORDER_MM, Array.make, wordsNat, n256MM]; decide

/-- The number a scalar's limbs encode. -/
abbrev scNat (s : mid.p256.Scalar) : Nat := wordsNat s.val

theorem repeat_length4 : (Array.repeat 4#usize core.default.DefaultU64.default).val.length = 4 := by
  simp [Array.repeat]

/-- A result written through a scalar's slice is the scalar with its limbs. -/
theorem from_slice4 (s s4 : Slice U64) (hs : s.val = (Array.repeat 4#usize core.default.DefaultU64.default).val)
    (h : s4.length = s.length) :
    ((Array.repeat 4#usize core.default.DefaultU64.default).from_slice s4).val = s4.val := by
  apply Array.from_slice_val
  rw [show s4.val.length = s4.length from rfl, h, Slice.length, hs, repeat_length4]; rfl

theorem slice_length4 (s : Slice U64) (hs : s.val = (Array.repeat 4#usize core.default.DefaultU64.default).val) :
    s.length = 4 := by
  rw [Slice.length, hs, repeat_length4]

theorem mul_lt_mont (a b : Nat) (ha : a < n256) (hb : b < n256) : a * b ≤ 2 ^ 256 * n256 :=
  le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (Nat.mul_le_mul_right _ (le_of_lt n256_lt)))

@[step]
theorem scalar_mont_mul_spec (a b : mid.p256.Scalar) (ha : scNat a < n256) (hb : scNat b < n256) :
    mid.p256.Scalar.mont_mul a b ⦃ r => scNat r = n256RInv * scNat a * scNat b % n256 ⦄ := by
  unfold mid.p256.Scalar.mont_mul mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice4 s s4 s_post s4_post]
  rw [slice_length4 s s_post, s1_post, s2_post, s3_post] at s4_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val] at s4_post1
  exact s4_post1 n256_odd (mul_lt_mont _ _ ha hb) n256RInv n256RInv_spec

@[step]
theorem scalar_as_mont_spec (a : mid.p256.Scalar) (ha : scNat a < n256) :
    mid.p256.Scalar.as_mont a ⦃ r => scNat r = 2 ^ 256 * scNat a % n256 ⦄ := by
  unfold mid.p256.Scalar.as_mont mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice4 s s4 s_post s4_post]
  rw [slice_length4 s s_post, s1_post, s2_post, s3_post] at s4_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val, CURVE_ORDER_MM_val] at s4_post1
  rw [s4_post1 n256_odd (mul_lt_mont _ _ ha n256MM_spec.1) n256RInv n256RInv_spec,
    show n256RInv * wordsNat a.val * n256MM = wordsNat a.val * (n256RInv * n256MM) by ring,
    Nat.mul_mod, n256MM_spec.2, ← Nat.mul_mod, Nat.mul_comm (wordsNat a.val)]

@[step]
theorem scalar_demont_spec (a : mid.p256.Scalar) :
    mid.p256.Scalar.demont a ⦃ r => scNat r = n256RInv * scNat a % n256 ⦄ := by
  unfold mid.p256.Scalar.demont mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice4 s s3 s_post s3_post]
  rw [slice_length4 s s_post, s1_post, s2_post] at s3_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val] at s3_post1
  exact s3_post1 n256_odd n256RInv n256RInv_spec

@[step]
theorem scalar_add_spec (a b : mid.p256.Scalar) (ha : scNat a < n256) (hb : scNat b < n256) :
    mid.p256.Scalar.add a b ⦃ r => scNat r = (scNat a + scNat b) % n256 ⦄ := by
  unfold mid.p256.Scalar.add mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  · simpa [s1_post, s3_post, CURVE_ORDER_val] using ha
  · simpa [s2_post, s3_post, CURVE_ORDER_val] using hb
  · rw [to_slice_mut_back_post, scNat, from_slice4 s s4 s_post s4_post]
    simpa [s1_post, s2_post, s3_post, CURVE_ORDER_val] using s4_post1

@[step]
theorem scalar_inv_spec (a : mid.p256.Scalar) (ha0 : 0 < scNat a) (ha : scNat a < n256) :
    mid.p256.Scalar.inv a ⦃ r => scNat r < n256 ∧ scNat a * scNat r % n256 = 1 ⦄ := by
  unfold mid.p256.Scalar.inv mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice4 s s4 s_post s4_post]
  rw [s1_post, s2_post] at s4_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val] at s4_post1
  exact s4_post1 ((prime_n256.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha0 ha)).symm)
    n256_odd (by unfold n256; decide)

instance : Fact (Nat.Prime n256) := ⟨prime_n256⟩

theorem n256_pos : 0 < n256 := prime_n256.pos

/-- A number below n is the value of its residue. -/
theorem val_of_eq (x : Nat) (z : ZMod n256) (hx : x < n256) (h : (x : ZMod n256) = z) : x = z.val := by
  rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

theorem RInv_mul : ((2 ^ 256 : Nat) : ZMod n256) * (n256RInv : ZMod n256) = 1 := by
  have := congrArg (fun x : Nat => (x : ZMod n256)) n256RInv_spec
  simpa [Nat.cast_mul] using this

/-- `raw_ecdsa_sign`: (e + rd)/k mod n. -/
theorem raw_ecdsa_sign_spec (d k : mid.p256.StaticPrivateKey) (e r : mid.p256.Scalar)
    (hd : scNat d.scalar < n256) (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n256)
    (he : scNat e < n256) (hr : scNat r < n256) :
    mid.p256.StaticPrivateKey.raw_ecdsa_sign d k e r ⦃ s =>
      scNat s = (((scNat e + scNat r * scNat d.scalar : Nat) : ZMod n256) *
        (scNat k.scalar : ZMod n256)⁻¹).val ⦄ := by
  unfold mid.p256.StaticPrivateKey.raw_ecdsa_sign low.ct.into_public
  have hlt : ∀ x, x % n256 < n256 := fun x => Nat.mod_lt _ n256_pos
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step with scalar_mont_mul_spec a b (by rw [ha]; exact hlt _) (by rw [hb]; exact hlt _) as ⟨c, hc⟩
  step as ⟨c1, hc1⟩
  step with scalar_add_spec c1 e (by rw [hc1]; exact hlt _) he as ⟨c2, hc2⟩
  step with scalar_as_mont_spec c2 (by rw [hc2]; exact hlt _) as ⟨l, hl⟩
  step with scalar_inv_spec k.scalar hk0 hk as ⟨ki, hki, hkk⟩
  step with scalar_mont_mul_spec ki l hki (by rw [hl]; exact hlt _) as ⟨s6, hs6⟩
  apply val_of_eq _ _ (by rw [hs6]; exact hlt _)
  have hk' : (scNat k.scalar : ZMod n256) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hk0 hk
  have hkk' : (scNat k.scalar : ZMod n256) * (scNat ki : ZMod n256) = 1 := by
    have := congrArg (fun x : Nat => (x : ZMod n256)) hkk
    simpa [Nat.cast_mul] using this
  have hkinv : (scNat ki : ZMod n256) = (scNat k.scalar : ZMod n256)⁻¹ := by
    exact (inv_eq_of_mul_eq_one_right hkk').symm
  simp only [scNat] at *
  rw [hs6, hl, hc2, hc1, hc, ha, hb]
  push_cast [ZMod.natCast_mod]
  rw [hkinv]
  have hR := RInv_mul
  push_cast at hR
  set t : ZMod n256 := (2 ^ 256 : ZMod n256) * (n256RInv : ZMod n256)
  linear_combination (scNat k.scalar : ZMod n256)⁻¹ *
    ((t ^ 2 + t + 1) * (scNat d.scalar : ZMod n256) * (scNat r : ZMod n256) + (scNat e : ZMod n256)) * hR

/-! ## Field elements, `mid::p256::FieldElement` -/

@[step]
theorem array_eq_spec (a b : Std.Array U64 4#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a b ⦃ r => r ↔ a.val = b.val ⦄ := by
  have : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a b =
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64 a.to_slice b.to_slice := by
    simp [core.array.equality.PartialEqArray.eq, core.slice.cmp.PartialEqSlice.eq, Array.val_to_slice]
  rw [this]
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ (fun x y => by simp [liftFun2]))
  intro r hr
  rw [hr, Slice.eq_iff, Array.val_to_slice, Array.val_to_slice]

theorem wordsNat_inj4 (a b : List U64) (ha : a.length = 4) (hb : b.length = 4)
    (h : wordsNat a = wordsNat b) : a = b := by
  match a, ha, b, hb with
  | [a0, a1, a2, a3], _, [b0, b1, b2, b3], _ =>
    have := a0.hBounds; have := a1.hBounds; have := a2.hBounds; have := a3.hBounds
    have := b0.hBounds; have := b1.hBounds; have := b2.hBounds; have := b3.hBounds
    simp only [UScalarTy.numBits] at *
    simp only [wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil] at h
    have e0 : a0.val = b0.val := by omega
    have e1 : a1.val = b1.val := by omega
    have e2 : a2.val = b2.val := by omega
    have e3 : a3.val = b3.val := by omega
    simp [UScalar.eq_of_val_eq e0, UScalar.eq_of_val_eq e1, UScalar.eq_of_val_eq e2,
      UScalar.eq_of_val_eq e3]

@[step]
theorem fe_public_eq_spec (a b : mid.p256.FieldElement) :
    mid.p256.FieldElement.public_eq a b ⦃ r => r ↔ feNat a = feNat b ⦄ := by
  unfold mid.p256.FieldElement.public_eq
  apply WP.spec_mono (array_eq_spec a b)
  intro r hr
  rw [hr]
  exact ⟨fun h => by simp [feNat, h], fun h => wordsNat_inj4 _ _ a.property b.property h⟩

@[step]
theorem fe_inv_spec (a : mid.p256.FieldElement) :
    mid.p256.FieldElement.inv a ⦃ r => feNat r < p256 ∧
      (feNat a % p256 ≠ 0 → feNat a * feNat r % p256 = 1) ∧ (feNat a % p256 = 0 → feNat r = 0) ⦄ := by
  unfold mid.p256.FieldElement.inv mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem fe_negate_spec (a : mid.p256.FieldElement) (ha : feNat a ≤ p256) :
    mid.p256.FieldElement.negate_mod_p a ⦃ r => feNat r = (p256 - feNat a) % p256 ⦄ := by
  unfold mid.p256.FieldElement.negate_mod_p mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

/-- A number's value as a field element in Montgomery form: it times 2⁻²⁵⁶. -/
abbrev dec (x : Nat) : ZMod p256 := (p256RInv : ZMod p256) * x

theorem R_mul_RInv : ((2 ^ 256 : Nat) : ZMod p256) * (p256RInv : ZMod p256) = 1 := by
  have := congrArg (fun n : Nat => (n : ZMod p256)) p256RInv_spec.2
  simpa only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] using this

theorem RInv_ne_zero : (p256RInv : ZMod p256) ≠ 0 := fun h => by
  have := R_mul_RInv; rw [h, mul_zero] at this; exact zero_ne_one this

theorem cast_mod_p (x : Nat) : ((x % p256 : Nat) : ZMod p256) = x := ZMod.natCast_mod _ _

/-- Numbers below p are equal when their values are. -/
theorem eq_of_dec (x y : Nat) (hx : x < p256) (hy : y < p256) : x = y ↔ dec x = dec y := by
  constructor
  · intro h; rw [h]
  · intro h
    have h' : (x : ZMod p256) = y := mul_left_cancel₀ RInv_ne_zero h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
    exact h'

theorem dec_mont_mul (a b : Nat) : dec (p256RInv * a * b % p256) = dec a * dec b := by
  simp only [dec, cast_mod_p, Nat.cast_mul]; ring

theorem dec_mont_sqr (a : Nat) : dec (p256RInv * a ^ 2 % p256) = dec a ^ 2 := by
  simp only [dec, cast_mod_p, Nat.cast_mul, Nat.cast_pow]; ring

theorem val_dec (x : Nat) : p256RInv * x % p256 = (dec x).val := by
  rw [dec, ← Nat.cast_mul, ZMod.val_natCast]

theorem ofJacobian_dec (x y z : Nat) :
    p256OfJacobian (p256RInv * x % p256) (p256RInv * y % p256) (p256RInv * z % p256) =
      if dec z = 0 then none
      else some ((dec x * (dec z ^ 2)⁻¹).val, (dec y * (dec z ^ 3)⁻¹).val) := by
  unfold p256OfJacobian
  simp only [val_dec, ZMod.natCast_val, ZMod.cast_id', id, ZMod.val_eq_zero]

/-- `pt` holds `P` in Jacobian Montgomery form, as s2n-bignum's routines read it. -/
def jrep (P : P256Point) (pt : mid.p256.JacobianMontPoint) : Prop :=
  p256Represents P (tripleNat pt.xyz.val)

@[step]
theorem jac_x_spec (pt : mid.p256.JacobianMontPoint) :
    mid.p256.JacobianMontPoint.x pt ⦃ fe => fe.val = (pt.xyz.val.drop 0).take 4 ⦄ := by
  unfold mid.p256.JacobianMontPoint.x
  have hl : (pt.xyz.val).length = 12 := pt.xyz.property
  step*
  · simp [mid.p256.JacobianMontPoint.X]
  · simp [mid.p256.JacobianMontPoint.X]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.JacobianMontPoint.X]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.JacobianMontPoint.X, List.slice]

@[step]
theorem jac_y_spec (pt : mid.p256.JacobianMontPoint) :
    mid.p256.JacobianMontPoint.y pt ⦃ fe => fe.val = (pt.xyz.val.drop 4).take 4 ⦄ := by
  unfold mid.p256.JacobianMontPoint.y
  have hl : (pt.xyz.val).length = 12 := pt.xyz.property
  step*
  · simp [mid.p256.JacobianMontPoint.Y]
  · simp [mid.p256.JacobianMontPoint.Y]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.JacobianMontPoint.Y]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.JacobianMontPoint.Y, List.slice]

@[step]
theorem jac_z_spec (pt : mid.p256.JacobianMontPoint) :
    mid.p256.JacobianMontPoint.z pt ⦃ fe => fe.val = (pt.xyz.val.drop 8).take 4 ⦄ := by
  unfold mid.p256.JacobianMontPoint.z
  have hl : (pt.xyz.val).length = 12 := pt.xyz.property
  step*
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [mid.p256.JacobianMontPoint.Z]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.JacobianMontPoint.Z]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.JacobianMontPoint.Z, List.slice]

theorem tripleNat_eq (pt : mid.p256.JacobianMontPoint) (fx fy fz : mid.p256.FieldElement)
    (hx : fx.val = (pt.xyz.val.drop 0).take 4) (hy : fy.val = (pt.xyz.val.drop 4).take 4)
    (hz : fz.val = (pt.xyz.val.drop 8).take 4) :
    tripleNat pt.xyz.val = (feNat fx, feNat fy, feNat fz) := by
  simp only [tripleNat, feNat, hx, hy, hz, List.drop_zero]

theorem jrep_iff (P : P256Point) (pt : mid.p256.JacobianMontPoint) (fx fy fz : mid.p256.FieldElement)
    (hx : fx.val = (pt.xyz.val.drop 0).take 4) (hy : fy.val = (pt.xyz.val.drop 4).take 4)
    (hz : fz.val = (pt.xyz.val.drop 8).take 4) :
    jrep P pt ↔ feNat fx < p256 ∧ feNat fy < p256 ∧ feNat fz < p256 ∧
      P = if dec (feNat fz) = 0 then none
        else some ((dec (feNat fx) * (dec (feNat fz) ^ 2)⁻¹).val,
          (dec (feNat fy) * (dec (feNat fz) ^ 3)⁻¹).val) := by
  rw [jrep, tripleNat_eq pt fx fy fz hx hy hz, p256Represents]
  simp only [ofJacobian_dec, eq_comm (a := P)]

@[step]
theorem infinity_spec : mid.p256.JacobianMontPoint.infinity ⦃ pt => jrep none pt ⦄ := by
  unfold mid.p256.JacobianMontPoint.infinity
  simp only [WP.spec_ok, jrep, p256Represents, tripleNat, Array.make]
  refine ⟨by simp [wordsNat, Nat.ofDigits, p256], by simp [wordsNat, Nat.ofDigits, p256],
    by simp [wordsNat, Nat.ofDigits, p256], ?_⟩
  simp [wordsNat, Nat.ofDigits, p256OfJacobian]

@[step]
theorem is_infinity_spec (pt : mid.p256.JacobianMontPoint) (P : P256Point) (h : jrep P pt) :
    mid.p256.JacobianMontPoint.public_is_infinity pt ⦃ b => b ↔ P = none ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_is_infinity mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step as ⟨fz, hfz⟩
  step as ⟨b, hb⟩
  have hz : (tripleNat pt.xyz.val).2.2 = feNat fz := by simp [tripleNat, feNat, hfz]
  obtain ⟨-, -, hzp, hP⟩ := h
  rw [ofJacobian_dec] at hP
  rw [hz] at hzp hP
  have h0 : feNat (Array.repeat 4#usize core.default.DefaultU64.default) = 0 := by
    simp [feNat, wordsNat, Array.repeat, Nat.ofDigits, core.default.DefaultU64.default]
  rw [hb, h0, ← hP]
  constructor
  · intro hz0; rw [hz0]; simp
  · intro hn
    by_contra hz0
    have : dec (feNat fz) ≠ 0 := fun hd => hz0 ((eq_of_dec _ 0 hzp p256_pos).mpr (by rw [hd]; simp))
    simp [this] at hn

theorem from_affine_val (p : mid.p256.AffineMontPoint) :
    mid.p256.JacobianMontPoint.from_affine p ⦃ pt => pt.xyz.val = p.xy.val ++ mid.p256.CURVE_ONE_MONT.val ⦄ := by
  unfold mid.p256.JacobianMontPoint.from_affine core.default.DefaultArray.default
  have hl : (p.xy.val).length = 8 := p.xy.property
  step*
  · simp [mid.p256.JacobianMontPoint.XY]
  · simp [mid.p256.JacobianMontPoint.XY]
  · simp [s_post1, s1_post, mid.p256.JacobianMontPoint.XY, hl]
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [mid.p256.JacobianMontPoint.Z]
  · simp [s3_post1, s4_post, mid.p256.JacobianMontPoint.Z, mid.p256.CURVE_ONE_MONT, Array.make]
  · rw [s3_post2, s5_post, s4_post, s2_post, s_post2, s1_post]
    simp only [mid.p256.JacobianMontPoint.XY, mid.p256.JacobianMontPoint.Z, Array.val_to_slice]
    generalize p.xy.val = l at hl ⊢
    match l, hl with
    | [a, b, c, d, e, f, g, h], _ =>
      simp [Array.repeat, mid.p256.CURVE_ONE_MONT, Array.make, List.setSlice!]

theorem CURVE_ONE_MONT_val : feNat mid.p256.CURVE_ONE_MONT = 2 ^ 256 % p256 := by
  simp only [feNat, mid.p256.CURVE_ONE_MONT, Array.make, wordsNat, p256]; decide

theorem dec_one : dec (2 ^ 256 % p256) = 1 := by
  rw [dec, cast_mod_p, mul_comm]; exact R_mul_RInv

theorem tripleNat_append (a b : List U64) (ha : a.length = 8) (hb : b.length = 4) :
    tripleNat (a ++ b) = ((pairNat a).1, (pairNat a).2, wordsNat b) := by
  simp [tripleNat, pairNat, List.take_append, List.drop_append, ha, hb, List.take_of_length_le]

/-- A pair of coordinates represents the point their values name. -/
theorem rep2_dec (P : P256Point) (xy : Nat × Nat) (h : p256Represents2 P xy) :
    xy.1 < p256 ∧ xy.2 < p256 ∧ P = some ((dec xy.1).val, (dec xy.2).val) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [← h3, val_dec, val_dec]⟩

@[step]
theorem from_affine_spec (p : mid.p256.AffineMontPoint) (P : P256Point)
    (h : p256Represents2 P (pairNat p.xy.val)) :
    mid.p256.JacobianMontPoint.from_affine p ⦃ pt => jrep P pt ⦄ := by
  apply WP.spec_mono (from_affine_val p)
  intro pt hpt
  obtain ⟨h1, h2, rfl⟩ := rep2_dec P _ h
  rw [jrep, hpt, tripleNat_append _ _ p.xy.property mid.p256.CURVE_ONE_MONT.property, p256Represents]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [show wordsNat mid.p256.CURVE_ONE_MONT.val = feNat mid.p256.CURVE_ONE_MONT from rfl, CURVE_ONE_MONT_val]
    exact Nat.mod_lt _ p256_pos
  · rw [ofJacobian_dec, show wordsNat mid.p256.CURVE_ONE_MONT.val = feNat mid.p256.CURVE_ONE_MONT from rfl,
      CURVE_ONE_MONT_val, dec_one]
    simp

@[step]
theorem double_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (P : P256Point) (h : jrep P pt) :
    mid.p256.JacobianMontPoint.double pt ⦃ r => jrep (p256Add P P) r ⦄ := by
  unfold mid.p256.JacobianMontPoint.double mid.p256.JacobianMontPoint.zero
  step*
  exact a_post P h

@[step]
theorem add_inplace_affine_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (p : mid.p256.AffineMontPoint)
    (P1 P2 : P256Point) (h1 : jrep P1 pt) (h2 : p256Represents2 P2 (pairNat p.xy.val)) (hne : P1 ≠ P2) :
    mid.p256.JacobianMontPoint.add_inplace_affine pt p ⦃ r => jrep (p256Add P1 P2) r ⦄ := by
  unfold mid.p256.JacobianMontPoint.add_inplace_affine
  step*
  exact a_post P1 P2 h1 h2 hne

@[step]
theorem jac_add_spec (_hr : Runs) (pt q : mid.p256.JacobianMontPoint) (P1 P2 : P256Point) (h1 : jrep P1 pt)
    (h2 : jrep P2 q) (hne : P1 = P2 → P2 = none) :
    mid.p256.JacobianMontPoint.add pt q ⦃ r => jrep (p256Add P1 P2) r ⦄ := by
  unfold mid.p256.JacobianMontPoint.add
  step*
  exact a_post P1 P2 h1 h2 hne

theorem onCurve_zmod (x y : Nat) (h : p256OnCurve (some (x, y))) :
    (y : ZMod p256) ^ 2 = (x : ZMod p256) ^ 3 + ((p256 - 3 : Nat) : ZMod p256) * x + (b256 : ZMod p256) := by
  obtain ⟨-, -, h⟩ := h
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
  push_cast at this
  exact this

/-- Two points of the curve with the same x and different y are opposite. -/
theorem neg_of_same_x (x y1 y2 : Nat) (h1 : p256OnCurve (some (x, y1))) (h2 : p256OnCurve (some (x, y2)))
    (hne : y1 ≠ y2) : some (x, y2) = p256Neg (some (x, y1)) := by
  have e1 := onCurve_zmod x y1 h1
  have e2 := onCurve_zmod x y2 h2
  have hne' : (y2 : ZMod p256) - y1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h2.2.1, Nat.mod_eq_of_lt h1.2.1] at h
    exact hne h.symm
  have hsum : (y2 : ZMod p256) + y1 = 0 := by
    have : ((y2 : ZMod p256) - y1) * ((y2 : ZMod p256) + y1) = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.mp this).resolve_left hne'
  simp only [p256Neg, nist.neg, Option.some.injEq, Prod.mk.injEq, true_and]
  have hlt : (p256 - y1 % p256) % p256 < p256 := Nat.mod_lt _ p256_pos
  rw [← Nat.mod_eq_of_lt h2.2.1, ← Nat.mod_eq_of_lt hlt, ← ZMod.natCast_eq_natCast_iff', nist.natCast_neg_mod]
  linear_combination hsum

theorem dec_lt (x : Nat) : (dec x).val < p256 := ZMod.val_lt _

theorem val_inj (a b : ZMod p256) : a.val = b.val ↔ a = b := ⟨fun h => ZMod.val_injective _ h, fun h => h ▸ rfl⟩

@[step]
theorem add_affine_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (p : mid.p256.AffineMontPoint)
    (P1 P2 : P256Point) (hc1 : p256OnCurve P1) (hc2 : p256OnCurve P2) (h1 : jrep P1 pt)
    (h2 : p256Represents2 P2 (pairNat p.xy.val)) :
    mid.p256.JacobianMontPoint.public_add_affine pt p ⦃ r => jrep (p256Add P1 P2) r ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_add_affine
  step with is_infinity_spec pt P1 h1 as ⟨b, hb⟩
  split
  · rename_i hbt
    rw [hb.mp hbt]
    step with from_affine_spec p P2 h2 as ⟨r, hr⟩
    rw [p256Laws.mul_none P2 hc2]; exact hr
  · rename_i hbf
    have hP1 : P1 ≠ none := fun h => hbf (hb.mpr h)
    obtain ⟨hpx, hpy, hP2⟩ := rep2_dec P2 _ h2
    have hl : (p.xy.val).length = 8 := p.xy.property
    obtain ⟨hX, hY, hZ, hP1eq⟩ := h1
    rw [ofJacobian_dec] at hP1eq
    set X := (tripleNat pt.xyz.val).1
    set Y := (tripleNat pt.xyz.val).2.1
    set Z := (tripleNat pt.xyz.val).2.2
    have hZ0 : dec Z ≠ 0 := fun h => hP1 (by rw [← hP1eq, ite_eq_left h])
    rw [ite_eq_right hZ0] at hP1eq
    set px := (pairNat p.xy.val).1
    set py := (pairNat p.xy.val).2
    have hlt : ∀ x, x % p256 < p256 := fun x => Nat.mod_lt _ p256_pos
    step as ⟨fz, hfz⟩
    have hfzZ : feNat fz = Z := by simp [Z, tripleNat, feNat, hfz]
    step with mont_sqr_spec _hr fz (by rw [hfzZ]; exact hZ) as ⟨z2, hz2⟩
    step as ⟨fe1, hfe1⟩
    have hfe1x : feNat fe1 = px := by simp [px, pairNat, feNat, hfe1]
    step with mont_mul_spec _hr fe1 z2 (by rw [hfe1x]; exact hpx) (by rw [hz2]; exact hlt _) as ⟨fe2, hfe2⟩
    step as ⟨fe3, hfe3⟩
    have hfe3X : feNat fe3 = X := by simp [X, tripleNat, feNat, hfe3]
    step as ⟨b1, hb1⟩
    have hxeq : b1 ↔ (dec px).val = (dec X * (dec Z ^ 2)⁻¹).val := by
      rw [hb1, hfe3X, eq_of_dec _ _ (by rw [hfe2]; exact hlt _) hX, hfe2, dec_mont_mul, hz2,
        dec_mont_sqr, hfzZ, hfe1x, val_inj, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hZ0)]
    split
    · rename_i hb1t
      have hxe := hxeq.mp hb1t
      step as ⟨fe4, hfe4⟩
      have hfe4y : feNat fe4 = py := by
        simp [py, pairNat, feNat, hfe4, List.take_of_length_le, hl]
      step with mont_mul_spec _hr z2 fz (by rw [hz2]; exact hlt _) (by rw [hfzZ]; exact hZ) as ⟨fe5, hfe5⟩
      step with mont_mul_spec _hr fe4 fe5 (by rw [hfe4y]; exact hpy) (by rw [hfe5]; exact hlt _) as ⟨fe6, hfe6⟩
      step as ⟨fe7, hfe7⟩
      have hfe7Y : feNat fe7 = Y := by simp [Y, tripleNat, feNat, hfe7]
      step as ⟨b2, hb2⟩
      have hyeq : b2 ↔ (dec py).val = (dec Y * (dec Z ^ 3)⁻¹).val := by
        rw [hb2, hfe7Y, eq_of_dec _ _ (by rw [hfe6]; exact hlt _) hY, hfe6, dec_mont_mul, hfe5,
          dec_mont_mul, hz2, dec_mont_sqr, hfzZ, hfe4y, val_inj,
          eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 3 hZ0)]
        constructor <;> intro h <;> linear_combination h
      have hP1' : jrep P1 pt := ⟨hX, hY, hZ, by rw [ofJacobian_dec, ite_eq_right hZ0, hP1eq]⟩
      split
      · rename_i hb2t
        have heq : P1 = P2 := by rw [← hP1eq, hP2, hxe, hyeq.mp hb2t]
        step with double_spec _hr pt P1 hP1' as ⟨r, hr⟩
        rw [← heq]; exact hr
      · rename_i hb2f
        have hneg : P2 = p256Neg P1 := by
          have hc1' := hc1
          have hc2' := hc2
          rw [← hP1eq, ← hxe] at hc1'
          rw [hP2] at hc2'
          rw [← hP1eq, hP2, ← hxe]
          refine neg_of_same_x _ _ _ hc1' hc2' ?_
          intro h; exact hb2f (hyeq.mpr h.symm)
        step as ⟨r, hr⟩
        rw [hneg, p256Laws.mul_neg P1 hc1]; exact hr
    · rename_i hb1f
      have hne : P1 ≠ P2 := by
        rw [← hP1eq, hP2]
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact hb1f (hxeq.mpr h.1.symm)
      step with add_inplace_affine_spec _hr pt p P1 P2 ⟨hX, hY, hZ, by rw [ofJacobian_dec, ite_eq_right hZ0, hP1eq]⟩ h2 hne
        as ⟨r, hr⟩
      exact hr

/-! ## Non-adjacent form, `mid::util::public_naf` -/

/-- The integer that little-endian signed digits name: d₀ + 2d₁ + 4d₂ + ⋯. -/
def nafVal : List I8 → Int
  | [] => 0
  | d :: ds => d.val + 2 * nafVal ds

theorem nafVal_append (l1 l2 : List I8) : nafVal (l1 ++ l2) = nafVal l1 + 2 ^ l1.length * nafVal l2 := by
  induction l1 with
  | nil => simp [nafVal]
  | cons d ds ih => simp only [List.cons_append, nafVal, ih, List.length_cons, pow_succ]; ring

/-- A digit of a width-`W` NAF: zero, or odd and below 2^(W-1) in magnitude. -/
def nafDigit (A : Int) (d : Int) : Prop := d = 0 ∨ (d % 2 = 1 ∧ -A < d ∧ d < A)

/-- One digit of the NAF, for `A` = 2^(W-1): the window `w` of the remainder
`R` = w + 2A·H yields digit `d`, and the next window and remainder halve what
is left, which stays within the halved bound `M`. -/
theorem naf_step (A w H b H' M : Int) (hA : A = 16 ∨ A = 32) (hw0 : 0 ≤ w) (hw : w ≤ 2 * A)
    (hH : H = b + 2 * H') (hb : b = 0 ∨ b = 1) (hH' : 0 ≤ H')
    (hR : w + 2 * A * H ≤ M) (hM : (∃ t, M = 2 * A * t) ∨ M ≤ A) (hM2 : M % 2 = 0 ∨ M ≤ 1) :
    let d := if w % 2 = 1 then (if w < A then w else w - 2 * A) else 0
    let w'' := (w - d) / 2 + b * A
    nafDigit A d ∧ 0 ≤ w'' ∧ w'' ≤ 2 * A ∧
      w + 2 * A * H - d = 2 * (w'' + 2 * A * H') ∧ w'' + 2 * A * H' ≤ M / 2 := by
  intro d w''
  subst hH
  obtain rfl | rfl := hA <;> obtain rfl | rfl := hb <;> rcases hM with ⟨t, rfl⟩ | hM <;>
    simp only [d, w'', nafDigit] <;> split_ifs <;> omega

theorem div_split_hi (a X r : Nat) (ha : a < 2 ^ 64) : (a + 2 ^ 64 * X) / 2 ^ (64 + r) = X / 2 ^ r := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt ha, Nat.zero_add]

theorem div_split_lo (a X r : Nat) (hr : r < 64) : (a + 2 ^ 64 * X) / 2 ^ r % 2 = a / 2 ^ r % 2 := by
  have h : 2 ^ 64 * X = 2 ^ r * (2 * (2 ^ (63 - r) * X)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]; congr 2; omega
  rw [h, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- Bit `i` of a number's four limbs is bit `i % 64` of limb `i / 64`, or zero
above them. -/
theorem wordsNat_bit (l : List U64) (hl : l.length = 4) (i : Nat) :
    wordsNat l / 2 ^ i % 2 = if i / 64 < 4 then (l[i / 64]!).val / 2 ^ (i % 64) % 2 else 0 := by
  rw [wordsNat_four l hl]
  have h0 := (l[0]!).hBounds; have h1 := (l[1]!).hBounds
  have h2 := (l[2]!).hBounds; have h3 := (l[3]!).hBounds
  simp only [UScalarTy.numBits] at h0 h1 h2 h3
  have hi : i = 64 * (i / 64) + i % 64 := (Nat.div_add_mod i 64).symm
  have hr : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  generalize i / 64 = q at hi ⊢
  generalize i % 64 = r at hi hr ⊢
  subst hi
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ 4 ≤ q) with rfl | rfl | rfl | rfl | hq
  · simp only [Nat.mul_zero, Nat.zero_add, show 0 < 4 from by norm_num, ↓reduceIte]
    exact div_split_lo _ _ _ hr
  · simp only [Nat.mul_one, show 1 < 4 from by norm_num, ↓reduceIte]
    rw [div_split_hi _ _ _ h0]; exact div_split_lo _ _ _ hr
  · simp only [show 2 < 4 from by norm_num, ↓reduceIte, show 64 * 2 + r = 64 + (64 + r) by omega]
    rw [div_split_hi _ _ _ h0, div_split_hi _ _ _ h1]; exact div_split_lo _ _ _ hr
  · simp only [show 3 < 4 from by norm_num, ↓reduceIte, show 64 * 3 + r = 64 + (64 + (64 + r)) by omega]
    rw [div_split_hi _ _ _ h0, div_split_hi _ _ _ h1, div_split_hi _ _ _ h2]
  · simp only [show ¬ q < 4 by omega, ↓reduceIte]
    rw [Nat.div_eq_of_lt]
    calc _ < 2 ^ 256 := by simp only [Nat.reducePow] at *; omega
      _ ≤ 2 ^ (64 * q + r) := Nat.pow_le_pow_right (by norm_num) (by omega)

@[step]
theorem bit_spec (k : Slice U64) (hk : k.length = 4) (i : Usize) :
    mid.util.bit k i ⦃ r => r.val = ((wordsNat k.val / 2 ^ i.val % 2 : Nat) : Int) ⦄ := by
  unfold mid.util.bit Shared0U64.Insts.CoreOpsBitShrUsizeU64.shr
  rw [wordsNat_bit _ hk]
  step as ⟨i1, hi1⟩
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok, Slice.getElem?_Usize_eq, hi1]
  have hkl : k.val.length = 4 := hk
  by_cases hq : i.val / 64 < 4
  · rw [ite_eq_left_iff.mpr (fun h => absurd hq h), List.getElem?_eq_getElem (by omega)]
    simp only
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3, _⟩
    step as ⟨i4, hi4, _⟩
    simp only [UScalar.hcast_val_eq]
    rw [hi4, UScalar.val_and, hi3, hi2, Nat.shiftRight_eq_div_pow, show (1#u64 : U64).val = 1 from rfl,
      Nat.and_one_is_mod, getElem_eq_getElem! _ _ (by omega)]
    have hv : (k.val[i.val / 64]!).val / 2 ^ (i.val % 64) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize (k.val[i.val / 64]!).val / 2 ^ (i.val % 64) % 2 = v at hv ⊢
    simp only [Int.bmod, IScalarTy.numBits]
    interval_cases v <;> decide
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hq), List.getElem?_eq_none (by omega)]
    simp

theorem i32_bv (x : I32) : x.bv = BitVec.ofInt IScalarTy.I32.numBits x.val :=
  BitVec.ofInt_toInt.symm

theorem i32_and_one (x : I32) (hx0 : 0 ≤ x.val) (hx : x.val ≤ 64) : (x &&& 1#i32).val = x.val % 2 := by
  have h : (x &&& 1#i32).val = (BitVec.ofInt IScalarTy.I32.numBits x.val &&& (1#i32).bv).toInt := by
    rw [← i32_bv]; rfl
  rw [h]
  generalize x.val = v at hx0 hx ⊢
  interval_cases v <;> decide

theorem M_facts (i w : Nat) (hw : w = 5 ∨ w = 6) (hi : i < 257) :
    ((∃ t, ((2 ^ 256 / 2 ^ i : Nat) : Int) = 2 * 2 ^ (w - 1) * t) ∨
        ((2 ^ 256 / 2 ^ i : Nat) : Int) ≤ 2 ^ (w - 1)) ∧
      (((2 ^ 256 / 2 ^ i : Nat) : Int) % 2 = 0 ∨ ((2 ^ 256 / 2 ^ i : Nat) : Int) ≤ 1) ∧
      ((2 ^ 256 / 2 ^ i : Nat) : Int) / 2 = ((2 ^ 256 / 2 ^ (i + 1) : Nat) : Int) := by
  have hpow : 2 ^ 256 / 2 ^ i = 2 ^ (256 - i) := Nat.pow_div (by omega) (by norm_num)
  have hpow1 : 2 ^ 256 / 2 ^ (i + 1) = 2 ^ 256 / 2 ^ i / 2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  rw [hpow1, hpow]
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : w ≤ 256 - i
    · left
      refine ⟨2 ^ (256 - i - w), ?_⟩
      push_cast
      rw [← pow_succ', ← pow_add]
      congr 1; omega
    · right
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
  · by_cases h : 256 - i = 0
    · right; rw [h]; norm_num
    · left; push_cast
      rw [show 256 - i = (256 - i - 1) + 1 by omega, pow_succ]; simp
  · push_cast
    norm_cast

/-- The NAF loop's state after `s` digits: the digits so far name `k` but for
the remainder `w` + 2^W·⌊k / 2^(s+W)⌋ times 2^s, which is at most 2^(256-s). -/
def nafInv (w : Nat) (K : Nat) (s : Nat) (digits : List I8) (window : Int) : Prop :=
  digits.length = 257 ∧ 0 ≤ window ∧ window ≤ 2 * 2 ^ (w - 1) ∧
    (K : Int) = nafVal (digits.take s) + 2 ^ s * (window + 2 * 2 ^ (w - 1) * ((K / 2 ^ (s + w) : Nat) : Int)) ∧
    window + 2 * 2 ^ (w - 1) * ((K / 2 ^ (s + w) : Nat) : Int) ≤ ((2 ^ 256 / 2 ^ s : Nat) : Int) ∧
    ∀ j < s, nafDigit (2 ^ (w - 1)) (digits[j]!).val

theorem nafVal_take_succ (l : List I8) (i : Nat) (hi : i < l.length) (d : I8) :
    nafVal ((l.set i d).take (i + 1)) = nafVal (l.take i) + 2 ^ i * d.val := by
  rw [List.take_add_one, List.getElem?_set_self hi, List.take_set_of_le (by omega), nafVal_append,
    List.length_take, Nat.min_eq_left (by omega)]
  simp [nafVal]

theorem naf_inv_step (w K i : Nat) (hw : w = 5 ∨ w = 6) (hi : i < 257) (ds : List I8) (win : Int)
    (hinv : nafInv w K i ds win) (dd : I8)
    (hdd : dd.val = if win % 2 = 1 then (if win < 2 ^ (w - 1) then win else win - 2 * 2 ^ (w - 1)) else 0) :
    nafInv w K (i + 1) (ds.set i dd)
      ((win - dd.val) / 2 + ((K / 2 ^ (i + w) % 2 : Nat) : Int) * 2 ^ (w - 1)) := by
  obtain ⟨hlen, hw0, hw2, hsum, hbound, hdig⟩ := hinv
  have hA : (2 : Int) ^ (w - 1) = 16 ∨ (2 : Int) ^ (w - 1) = 32 := by
    rcases hw with rfl | rfl <;> norm_num
  have hH : ((K / 2 ^ (i + w) : Nat) : Int) =
      ((K / 2 ^ (i + w) % 2 : Nat) : Int) + 2 * ((K / 2 ^ (i + 1 + w) : Nat) : Int) := by
    have : K / 2 ^ (i + 1 + w) = K / 2 ^ (i + w) / 2 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]; congr 2; omega
    rw [this]; push_cast; omega
  have hb : ((K / 2 ^ (i + w) % 2 : Nat) : Int) = 0 ∨ ((K / 2 ^ (i + w) % 2 : Nat) : Int) = 1 := by
    have := Nat.mod_lt (K / 2 ^ (i + w)) (by norm_num : 2 > 0); omega
  obtain ⟨hM1, hM2, hM3⟩ := M_facts i w hw hi
  obtain ⟨hd, hw0', hw2', hR, hR'⟩ := naf_step _ _ _ _ _ _ hA hw0 hw2 hH hb (by positivity) hbound hM1 hM2
  rw [← hdd] at hd hw0' hw2' hR hR'
  rw [hM3] at hR'
  refine ⟨by simp [hlen], hw0', hw2', ?_, hR', ?_⟩
  · rw [nafVal_take_succ _ _ (by omega), pow_succ]
    have e : (2 : Int) ^ i * (win + 2 * 2 ^ (w - 1) * ((K / 2 ^ (i + w) : Nat) : Int)) =
        2 ^ i * dd.val + 2 ^ i * (2 * ((win - dd.val) / 2 + ((K / 2 ^ (i + w) % 2 : Nat) : Int) * 2 ^ (w - 1) +
          2 * 2 ^ (w - 1) * ((K / 2 ^ (i + 1 + w) : Nat) : Int))) := by
      rw [← hR]; ring
    rw [hsum, e, show i + 1 + w = i + w + 1 by omega]
    ring
  · intro j hj
    by_cases hji : j = i
    · subst hji
      have : (ds.set j dd)[j]! = dd := by
        simp [show j < ds.length by omega]
      rw [this]; exact hd
    · have : (ds.set i dd)[j]! = ds[j]! := by
        simp [List.getElem!_eq_getElem?_getD, Ne.symm hji]
      rw [this]; exact hdig j (by omega)

set_option exponentiation.threshold 257 in
theorem naf_loop_spec (W : U32) (hW : W.val = 5 ∨ W.val = 6) (k : Slice U64) (hk : k.length = 4)
    (iter : core.ops.range.Range Usize) (digits : Slice I8) (window : I32)
    (he : iter.end.val = 257) (hs : iter.start.val ≤ 257)
    (hinv : nafInv W.val (wordsNat k.val) iter.start.val digits.val window.val) :
    mid.util.public_naf_loop W iter k digits window ⦃ r =>
      r.length = 257 ∧ nafVal r.val = wordsNat k.val ∧ ∀ j < 257, nafDigit (2 ^ (W.val - 1)) (r.val[j]!).val ⦄ := by
  unfold mid.util.public_naf_loop
  apply loop.spec_decr_nat (fun x => 257 - x.1.start.val)
    (fun x => x.1.end.val = 257 ∧ x.1.start.val ≤ 257 ∧ nafInv W.val (wordsNat k.val) x.1.start.val x.2.1.val x.2.2.val)
  · rintro ⟨it, ds, win⟩ ⟨he, hs, hinv⟩
    simp only at he hs hinv ⊢
    obtain ⟨hlen, hw0, hw, hsum, hbound, hdig⟩ := hinv
    unfold mid.util.public_naf_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have hi : it.start.val < ds.length := by simp [Slice.length, hlen]; omega
      step with Slice.index_mut_usize_spec ds it.start hi as ⟨x, back, hx, hback⟩
      step as ⟨i1, hi1, _⟩
      have hA : (2 : Int) ^ (W.val - 1) = 16 ∨ (2 : Int) ^ (W.val - 1) = 32 := by
        rcases hW with h | h <;> rw [h] <;> norm_num
      rw [i32_and_one win hw0 (by omega)] at hi1
      have hWv : (W.val : Int) = 5 ∨ (W.val : Int) = 6 := by omega
      have hA2 : (2 : Int) ^ W.val = 2 * 2 ^ (W.val - 1) := by
        rw [← pow_succ']; congr 1; omega
      apply WP.spec_bind (Pₘ := fun r : Slice I8 × I32 × core.ops.range.Range Usize =>
        r.2.2 = iter1 ∧ ∃ dd : I8, r.1.val = ds.val.set it.start.val dd ∧ r.2.1.val = win.val - dd.val ∧
          dd.val = if win.val % 2 = 1 then (if win.val < 2 ^ (W.val - 1) then win.val
            else win.val - 2 * 2 ^ (W.val - 1)) else 0)
      · split
        · rename_i hodd
          have hodd' : win.val % 2 = 1 := by rw [← hi1, (IScalar.eq_equiv _ _).mp hodd]; rfl
          step as ⟨i2, hi2⟩
          step as ⟨i3, hi3, _⟩
          · rw [hi2]; scalar_tac
          have hi3v : i3.val = 2 ^ (W.val - 1) := by
            rw [hi3, hi2, Int.shiftLeft_eq, one_mul]
            rw [I32.size_def]
            exact Int.bmod_eq_of_le (by rcases hA with h | h <;> rw [h] <;> norm_num [I32.numBits])
              (by rcases hA with h | h <;> rw [h] <;> norm_num [I32.numBits])
          have hset : ∀ (d : I8), ((back 0#i8).set it.start d).val = ds.val.set it.start.val d := by
            intro d; rw [hback, Slice.set_val_eq, Slice.set_val_eq, List.set_set]
          by_cases hlo : win.val < 2 ^ (W.val - 1)
          · have hc : win < i3 := (IScalar.lt_equiv _ _).mpr (by rw [hi3v]; exact hlo)
            rw [ite_eq_left_iff.mpr (fun h => absurd hc h)]
            step as ⟨w2, hw2⟩
            step as ⟨i4, hi4⟩
            step as ⟨s', hs'⟩
            · (try rw [hback]); (try simp only [Slice.length, Slice.set_val_eq, List.length_set]); (try omega)
            have hi4v : i4.val = win.val := by
              rw [hi4, IScalar.cast_val_eq]
              exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
            refine ⟨i4, by rw [hs', hset], by rw [hw2, hi4v], by rw [hi4v]; simp [hodd', hlo]⟩
          · have hc : ¬ win < i3 := fun h => hlo (by rw [← hi3v]; exact (IScalar.lt_equiv _ _).mp h)
            rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]
            step as ⟨i5, hi5, _⟩
            · omega
            have hi5v : i5.val = 2 * 2 ^ (W.val - 1) := by
              rw [hi5, Int.shiftLeft_eq, one_mul]
              rw [I32.size_def]
              exact Int.bmod_eq_of_le (by rcases hA with h | h <;> rw [hA2, h] <;> norm_num [I32.numBits])
                (by rcases hA with h | h <;> rw [hA2, h] <;> norm_num [I32.numBits]) |>.trans hA2
            step as ⟨d, hd⟩
            step as ⟨w2, hw2⟩
            step as ⟨i4, hi4⟩
            step as ⟨s', hs'⟩
            · (try rw [hback]); (try simp only [Slice.length, Slice.set_val_eq, List.length_set]); (try omega)
            have hi4v : i4.val = d.val := by
              rw [hi4, IScalar.cast_val_eq]
              exact Int.bmod_eq_of_le (by rw [hd, hi5v]; simp; omega) (by rw [hd, hi5v]; simp; omega)
            refine ⟨i4, by rw [hs', hset], by rw [hw2, hi4v], by rw [hi4v, hd, hi5v]; simp [hodd', hlo]⟩
        · rename_i heven
          have heven' : win.val % 2 = 0 := by
            have : i1.val ≠ 1 := fun h => heven ((IScalar.eq_equiv _ _).mpr (by rw [h]; rfl))
            omega
          simp only [WP.spec_ok, true_and]
          exact ⟨0#i8, by rw [hback, Slice.set_val_eq], by simp, by simp [heven']⟩
      · rintro ⟨d1, w1, it2⟩ ⟨rfl, dd, hd1, hw1, hdd⟩
        have hnew := naf_inv_step W.val (wordsNat k.val) it.start.val hW (by omega) ds.val win.val
          ⟨hlen, hw0, hw, hsum, hbound, hdig⟩ dd hdd
        have hw1r : 0 ≤ w1.val ∧ w1.val ≤ 2 * 2 ^ (W.val - 1) := by
          rw [hw1, hdd]; rcases hA with h | h <;> rw [h] <;> split_ifs <;> omega
        step as ⟨i2, hi2, _⟩
        step as ⟨i3, hi3⟩
        have hi3v : i3.val = W.val := by
          rw [hi3, UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
        step as ⟨i4, hi4⟩
        · rw [hi3v]; scalar_tac
        step with bit_spec k hk i4 as ⟨i5, hi5⟩
        step as ⟨i6, hi6⟩
        step as ⟨i7, hi7, _⟩
        · rw [hi6]; omega
        have hi2v : i2.val = w1.val / 2 := by rw [hi2, Int.shiftRight_eq_div_pow]; norm_num
        have hbit : i5.val = ((wordsNat k.val / 2 ^ (it.start.val + W.val) % 2 : Nat) : Int) := by
          rw [hi5, hi4, hi3v]
        have hb01 : i5.val = 0 ∨ i5.val = 1 := by
          rw [hbit]; have := Nat.mod_lt (wordsNat k.val / 2 ^ (it.start.val + W.val)) (by norm_num : 2 > 0)
          omega
        have hi7v : i7.val = i5.val * 2 ^ (W.val - 1) := by
          rw [hi7, Int.shiftLeft_eq, hi6, I32.size_def]
          apply Int.bmod_eq_of_le <;> rcases hb01 with h | h <;> rw [h] <;>
            rcases hA with h' | h' <;> rw [h'] <;> norm_num [I32.numBits]
        step as ⟨w3, hw3⟩
        · rw [hi2v, hi7v]; rcases hb01 with h | h <;> rw [h] <;> rcases hA with h' | h' <;> rw [h'] <;>
            scalar_tac
        simp only at he1 hst
        refine ⟨by rw [he1]; exact he, by omega, ?_, by omega⟩
        rw [show it2.start.val = it.start.val + 1 by omega]
        have hd1' : d1.val = ds.val.set it.start.val dd := hd1
        have hw3' : w3.val = (win.val - dd.val) / 2 +
            ((wordsNat k.val / 2 ^ (it.start.val + W.val) % 2 : Nat) : Int) * 2 ^ (W.val - 1) := by
          rw [hw3, hi2v, hi7v, hw1, hbit]
        rw [hd1', hw3']
        exact hnew
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have h257 : it.start.val = 257 := by omega
      rw [h257] at hsum hbound hdig
      have hz : (2 ^ 256 / 2 ^ 257 : Nat) = 0 := Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
      rw [hz] at hbound
      have hK : wordsNat k.val / 2 ^ (257 + W.val) = 0 := Nat.div_eq_of_lt (by
        calc wordsNat k.val < 2 ^ 256 := by
              rw [wordsNat_four _ hk]
              have := (k.val[0]!).hBounds; have := (k.val[1]!).hBounds
              have := (k.val[2]!).hBounds; have := (k.val[3]!).hBounds
              simp only [UScalarTy.numBits, Nat.reducePow] at *; omega
          _ ≤ 2 ^ (257 + W.val) := Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hK] at hsum hbound
      refine ⟨hlen, ?_, hdig⟩
      have hwz : win.val = 0 := by push_cast at hbound; omega
      rw [hwz] at hsum
      rw [List.take_of_length_le (by rw [hlen])] at hsum
      simp at hsum; omega
  · exact ⟨he, hs, hinv⟩

theorem wordsNat_mod (l : List U64) (hl : l.length = 4) (w : Nat) (hw : w ≤ 64) :
    wordsNat l % 2 ^ w = (l[0]!).val % 2 ^ w := by
  rw [wordsNat_four l hl]
  have h : 2 ^ 64 = 2 ^ w * 2 ^ (64 - w) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem naf_spec (W : U32) (hW : W.val = 5 ∨ W.val = 6) (k : Slice U64) (hk : k.length = 4)
    (digits : Slice I8) (hd : digits.length = 257) :
    mid.util.public_naf W k digits ⦃ r =>
      r.length = 257 ∧ nafVal r.val = wordsNat k.val ∧ ∀ j < 257, nafDigit (2 ^ (W.val - 1)) (r.val[j]!).val ⦄ := by
  unfold mid.util.public_naf
  have hkl : k.val.length = 4 := hk
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, _⟩
  · omega
  have hi1v : i1.val = 2 ^ W.val := by
    rw [hi1, Nat.shiftLeft_eq, one_mul]; apply Nat.mod_eq_of_lt
    rcases hW with h | h <;> rw [h] <;> norm_num [U64.size, U64.numBits]
  step as ⟨i2, hi2⟩
  · rw [hi1v]; (try simp)
  step as ⟨i3, hi3, _⟩
  step as ⟨win, hwin⟩
  have hK : wordsNat k.val < 2 ^ 256 := by
    rw [wordsNat_four _ hk]
    have := (k.val[0]!).hBounds; have := (k.val[1]!).hBounds
    have := (k.val[2]!).hBounds; have := (k.val[3]!).hBounds
    simp only [UScalarTy.numBits, Nat.reducePow] at *; omega
  have hW64 : W.val ≤ 64 := by omega
  have hi3v : i3.val = wordsNat k.val % 2 ^ W.val := by
    rw [hi3, UScalar.val_and, hi2, hi1v, Nat.and_two_pow_sub_one_eq_mod, hi,
      wordsNat_mod _ hkl _ hW64]
    (try rw [getElem_eq_getElem! _ _ (by omega)])
  have hA2 : (2 : Nat) ^ W.val = 2 * 2 ^ (W.val - 1) := by rw [← pow_succ']; congr 1; omega
  have hwinv : win.val = ((wordsNat k.val % 2 ^ W.val : Nat) : Int) := by
    rw [hwin, UScalar.hcast_val_eq, hi3v]
    apply Int.bmod_eq_of_le <;>
      · have := Nat.mod_lt (wordsNat k.val) (show 2 ^ W.val > 0 by positivity)
        rcases hW with h | h <;> rw [h] at this ⊢ <;> norm_num [IScalarTy.numBits] at this ⊢ <;> omega
  apply naf_loop_spec W hW k hk _ digits win (by simp [Slice.len, hd]) (by simp)
  have hA2' : (2 : Int) * 2 ^ (W.val - 1) = ((2 ^ W.val : Nat) : Int) := by
    rw [hA2]; push_cast; ring
  have h0 : (0#usize).val = 0 := rfl
  refine ⟨hd, ?_, ?_, ?_, ?_, fun j hj => absurd hj (by simp)⟩
  · rw [hwinv]; positivity
  · rw [hwinv, hA2']
    exact_mod_cast (Nat.mod_lt (wordsNat k.val) (show 2 ^ W.val > 0 by positivity)).le
  · rw [h0, List.take_zero, Nat.zero_add, hwinv, hA2']
    simp only [nafVal, pow_zero, one_mul, zero_add]
    exact_mod_cast (Nat.mod_add_div _ _).symm
  · rw [h0, Nat.zero_add, hwinv, hA2', pow_zero, Nat.div_one]
    exact_mod_cast (show wordsNat k.val % 2 ^ W.val + 2 ^ W.val * (wordsNat k.val / 2 ^ W.val) ≤ 2 ^ 256 by
      rw [Nat.mod_add_div]; omega)

@[step]
theorem scalar_naf_spec (W : U32) (hW : W.val = 5 ∨ W.val = 6) (s : mid.p256.Scalar) :
    mid.p256.Scalar.public_naf W s ⦃ ds =>
      nafVal ds.val = scNat s ∧ ∀ j < 257, nafDigit (2 ^ (W.val - 1)) (ds.val[j]!).val ⦄ := by
  unfold mid.p256.Scalar.public_naf
  step as ⟨sl, hsl⟩
  step as ⟨s1, back, hs1, hback⟩
  step with naf_spec W hW sl (by rw [hsl]; simp) s1
      (by rw [Slice.length, hs1]; exact (Array.repeat 257#usize 0#i8).property) as
    ⟨s2, hl2, hv2, hd2⟩
  have hv : (back s2).val = s2.val := by
    rw [hback]; exact Array.from_slice_val _ _ (by simpa [Slice.length] using hl2)
  rw [hv, hsl] at *
  exact ⟨by simpa [Array.val_to_slice] using hv2, hd2⟩

theorem neg_val (v : ZMod p256) : (p256 - v.val % p256) % p256 = (-v).val := by
  have h := nist.natCast_neg_mod (p := p256) v.val
  rw [ZMod.natCast_val, ZMod.cast_id', id] at h
  rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ p256_pos)]

theorem dec_neg (y : Nat) (hy : y < p256) : dec ((p256 - y) % p256) = -(dec y) := by
  have := nist.natCast_neg_mod (p := p256) y
  rw [Nat.mod_eq_of_lt hy] at this
  simp only [dec]; rw [this]; ring

/-- `negate_y`: the point's opposite, `p256Neg`. -/
@[step]
theorem negate_y_spec (pt : mid.p256.AffineMontPoint) (P : P256Point)
    (h : p256Represents2 P (pairNat pt.xy.val)) :
    mid.p256.AffineMontPoint.negate_y pt ⦃ r => p256Represents2 (p256Neg P) (pairNat r.xy.val) ⦄ := by
  unfold mid.p256.AffineMontPoint.negate_y
  have hl : (pt.xy.val).length = 8 := pt.xy.property
  obtain ⟨hx, hy, rfl⟩ := rep2_dec P _ h
  step as ⟨fy, hfy⟩
  have hfyv : feNat fy = (pairNat pt.xy.val).2 := by
    simp [feNat, hfy, pairNat, List.take_of_length_le, hl]
  step with fe_negate_spec fy (by rw [hfyv]; omega) as ⟨ny, hny⟩
  step*
  · simp [mid.p256.AffineMontPoint.Y]
  · simp [mid.p256.AffineMontPoint.Y]
  · simp [s_post1, s1_post, mid.p256.AffineMontPoint.Y]
  · have hny' : ny.val.length = 4 := ny.property
    have hv : (index_mut_back s2).val = pt.xy.val.take 4 ++ ny.val := by
      rw [s_post2, s2_post, s1_post, Array.val_to_slice]
      simp only [mid.p256.AffineMontPoint.Y]
      generalize pt.xy.val = l at hl ⊢
      match l, hl with
      | [a, b, c, d, e, f, g, h'], _ =>
        generalize ny.val = m at hny' ⊢
        match m, hny' with
        | [a', b', c', d'], _ => simp [List.setSlice!]
    rw [hv, pairNat_append _ _ (by simp [hl]) hny']
    simp only [p256Neg]
    refine ⟨by simpa [pairNat] using hx, ?_, ?_⟩
    · rw [show wordsNat ny.val = feNat ny from rfl, hny]; exact Nat.mod_lt _ p256_pos
    · congr 2
      · rw [val_dec]; rfl
      · rw [show wordsNat ny.val = feNat ny from rfl, hny, hfyv, neg_val]
        dsimp only
        rw [val_dec, dec_neg _ hy]

/-! ## Twin multiplication, `JacobianMontPoint::public_twin_multiply` -/

@[step]
theorem rev_next_spec (r : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r ⦃ o r' =>
      r'.iter.start = r.iter.start ∧
        (if r.iter.start.val < r.iter.end.val then o = some r'.iter.end ∧ r'.iter.end.val + 1 = r.iter.end.val
          else o = none) ⦄ := by
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  simp only [
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked]
  by_cases hlt : r.iter.start.val < r.iter.end.val
  · have hb : liftFun2 core.cmp.impls.PartialOrdUsize.lt r.iter.start r.iter.end = ok true := by
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt]
    have h1 : (1#usize).val ≤ r.iter.end.val := by simp; omega
    simp only [hb, bind_ok, ↓reduceIte, h1, ↓reduceDIte, hlt]
    simp [UScalar.ofNatCore_val_eq]; omega
  · have hb : liftFun2 core.cmp.impls.PartialOrdUsize.lt r.iter.start r.iter.end = ok false := by
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt]
    simp [hb, hlt, WP.spec_ok]

theorem pairNat_take8 (l : List U64) : pairNat (l.take 8) = pairNat l := by
  simp [pairNat, List.take_take, List.drop_take]

theorem lookup_spec (row : Slice U64) (hrow : 256 ≤ row.length) (idx : U8) (h1 : 1 ≤ idx.val)
    (h32 : idx.val ≤ 32) :
    mid.p256.AffineMontPoint.public_lookup row idx ⦃ pt =>
      pairNat pt.xy.val = pairNat (row.val.drop (8 * (idx.val - 1))) ⦄ := by
  unfold mid.p256.AffineMontPoint.public_lookup core.slice.Slice.as_chunks
  have h8 : (8#usize).val = 8 := rfl
  simp only [h8, show (8 : Nat) ≠ 0 by norm_num, ↓reduceIte, bind_ok]
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hiv : i.val = idx.val := by rw [hi, UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
  step as ⟨a, ha⟩
  · simp only [Slice.length, Slice.from_val, List.length_ofFn] at hrow ⊢; omega
  rw [ha]
  simp only [Slice.from_val, List.getElem_ofFn, Array.from_val, Fin.val_cast, pairNat_take8]
  congr 2; rw [hi1, hiv]; ring

@[step]
theorem unsigned_abs_spec (x : I8) : core.num.I8.unsigned_abs x ⦃ r => r.val = x.val.natAbs ⦄ := by
  unfold core.num.I8.unsigned_abs
  simp only [WP.spec_ok]
  have := x.hBounds
  simp only [IScalarTy.numBits] at this
  show (BitVec.ofNat 8 x.val.natAbs).toNat = _
  rw [BitVec.toNat_ofNat]; omega

instance : Inhabited mid.p256.AffineMontPoint := ⟨⟨Array.repeat 8#usize 0#u64⟩⟩

/-- `odd` holds Q's odd multiples from `base`: entry i is Q times 2i + base. -/
def OddMultiples (Q : P256Point) (base : Nat) (odd : Std.Array mid.p256.AffineMontPoint 8#usize) : Prop :=
  ∀ i < 8, p256Represents2 (p256Pow Q (2 * i + base)) (pairNat (odd.val[i]!).xy.val)

theorem nafVal_drop (l : List I8) (i : Nat) (hi : i < l.length) :
    nafVal (l.drop i) = (l[i]!).val + 2 * nafVal (l.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, nafVal, getElem_eq_getElem! _ _ hi]

theorem i8_natAbs (d : I8) (A : Int) (hA : A = 16 ∨ A = 32) (hd : nafDigit A d.val) (hne : d.val ≠ 0) :
    d.val.natAbs % 2 = 1 ∧ d.val.natAbs < A.toNat := by
  rcases hd with h | ⟨h1, h2, h3⟩
  · exact absurd h hne
  · rcases hA with rfl | rfl <;> omega

/-- The point a nonzero digit names, as the twin multiplication looks it up. -/
theorem digit_point (P : P256Point) (hP : p256OnCurve P) (d : I8) (pt : mid.p256.AffineMontPoint)
    (hpt : p256Represents2 (p256Pow P d.val.natAbs) (pairNat pt.xy.val)) :
    (if d < 0#i8 then mid.p256.AffineMontPoint.negate_y pt else ok pt) ⦃ r =>
      p256Represents2 (p256ZPow P d.val) (pairNat r.xy.val) ⦄ := by
  split
  · rename_i hneg
    have hneg' : d.val < 0 := by simpa using (IScalar.lt_equiv _ _).mp hneg
    apply WP.spec_mono (negate_y_spec pt _ hpt)
    intro r hr
    rwa [← P256Laws.zpow_natCast, p256Laws.neg_zpow P hP, show -(d.val.natAbs : Int) = d.val by omega] at hr
  · rename_i hpos
    have hpos' : ¬ d.val < 0 := fun h => hpos ((IScalar.lt_equiv _ _).mpr (by simpa using h))
    simp only [WP.spec_ok]
    rwa [← P256Laws.zpow_natCast, show (d.val.natAbs : Int) = d.val by omega] at hpt

theorem twin_loop_spec (_hr : Runs) (Q : P256Point) (hQ : p256OnCurve Q)
    (odd : Std.Array mid.p256.AffineMontPoint 8#usize) (hodd : OddMultiples Q 1 odd)
    (more : Option (Std.Array mid.p256.AffineMontPoint 8#usize))
    (hmore : ∀ m, more = some m → OddMultiples Q 17 m)
    (g p : Std.Array I8 257#usize) (hg : ∀ j < 257, nafDigit 32 (g.val[j]!).val)
    (hp : ∀ j < 257, nafDigit (if more = none then 16 else 32) (p.val[j]!).val)
    (gm : Slice U64) (hgm : p256GRow gm.val)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (hs : iter.iter.start.val = 0)
    (he : iter.iter.end.val ≤ 257) (result : mid.p256.JacobianMontPoint)
    (hres : jrep (twin p256G Q (nafVal (g.val.drop iter.iter.end.val)) (nafVal (p.val.drop iter.iter.end.val)))
      result) :
    mid.p256.JacobianMontPoint.public_twin_multiply_loop iter odd more g p gm result ⦃ r =>
      jrep (twin p256G Q (nafVal g.val) (nafVal p.val)) r ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_twin_multiply_loop
  have hGc := p256OnCurve_G
  apply loop.spec_decr_nat (fun x => x.1.iter.end.val)
    (fun x => x.1.iter.start.val = 0 ∧ x.1.iter.end.val ≤ 257 ∧ x.2.1 = more ∧
      jrep (twin p256G Q (nafVal (g.val.drop x.1.iter.end.val)) (nafVal (p.val.drop x.1.iter.end.val))) x.2.2)
  · rintro ⟨it, m1, res⟩ ⟨hs, he, hm1, hres⟩
    simp only at hs he hm1 hres ⊢
    rw [hm1]
    unfold mid.p256.JacobianMontPoint.public_twin_multiply_loop.body
    step as ⟨o, it1, hst, ho⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, he1⟩ := ho
      simp only
      set A := nafVal (g.val.drop it.iter.end.val)
      set B := nafVal (p.val.drop it.iter.end.val)
      have hi : it1.iter.end.val < 257 := by omega
      have hgl : g.val.length = 257 := g.property
      have hpl : p.val.length = 257 := p.property
      step as ⟨gd, hgd⟩
      step as ⟨pd, hpd⟩
      have hgd' : gd = g.val[it1.iter.end.val]! := by rw [hgd, getElem_eq_getElem! _ _ (by omega)]
      have hpd' : pd = p.val[it1.iter.end.val]! := by rw [hpd, getElem_eq_getElem! _ _ (by omega)]
      step with is_infinity_spec res _ hres as ⟨b, hb⟩
      have hT := p256Laws.twin_onCurve p256G Q hGc hQ
      apply WP.spec_bind (Pₘ := fun r1 => jrep (twin p256G Q (2 * A) (2 * B)) r1)
      · split
        · rename_i hbt
          simp only [WP.spec_ok]
          have h0 := hb.mp hbt
          rw [← p256Laws.twin_double p256G Q hGc hQ, h0, p256Laws.mul_none none trivial, ← h0]
          exact hres
        · step with double_spec _hr res _ hres as ⟨r1, hr1⟩
          rwa [p256Laws.twin_double p256G Q hGc hQ] at hr1
      intro r1 hr1
      apply WP.spec_bind (Pₘ := fun x : Option (Std.Array mid.p256.AffineMontPoint 8#usize) ×
          mid.p256.JacobianMontPoint => x.1 = more ∧ jrep (twin p256G Q (2 * A) (2 * B + pd.val)) x.2)
      · split
        · rename_i hpne
          have hpv : pd.val ≠ 0 := by
            intro h
            have : pd = 0#i8 := (IScalar.eq_equiv _ _).mpr (by rw [h]; rfl)
            simp [this] at hpne
          have hdig := hp it1.iter.end.val hi
          rw [← hpd'] at hdig
          have hA' : (if more = none then (16 : Int) else 32) = 16 ∨ (if more = none then (16 : Int) else 32) = 32 := by
            split <;> simp
          obtain ⟨hodd', hlt'⟩ := i8_natAbs pd _ hA' hdig hpv
          step as ⟨i1, hi1⟩
          step as ⟨i2, hi2⟩
          simp only [lift, bind_ok]
          generalize hi3 : core.convert.num.FromUsizeU8.from i2 = i3
          have hi3v : i3.val = pd.val.natAbs / 2 := by
            rw [← hi3, core.convert.num.FromUsizeU8.from_val_eq, hi2, hi1]
          have h2i3 : 2 * i3.val + 1 = pd.val.natAbs := by omega
          apply WP.spec_bind (Pₘ := fun tmp : mid.p256.AffineMontPoint =>
            p256Represents2 (p256Pow Q pd.val.natAbs) (pairNat tmp.xy.val))
          · rcases hmo : more with _ | m
            · simp only [hmo, ↓reduceIte] at hlt'
              have h8 : i3.val < 8 := by omega
              step as ⟨tmp, htmp⟩
              rw [htmp, getElem_eq_getElem! _ _ (by simp; omega), ← h2i3]
              exact hodd _ h8
            · simp only [hmo, reduceCtorEq, ↓reduceIte] at hlt'
              simp only
              split
              · rename_i hge
                have hge' : 8 ≤ i3.val := by simpa using hge
                step as ⟨i4, hi4⟩
                step as ⟨tmp, htmp⟩
                rw [htmp, getElem_eq_getElem! _ _ (by simp; omega)]
                have := hmore m hmo (i4.val) (by omega)
                rwa [show 2 * i4.val + 17 = pd.val.natAbs by omega] at this
              · rename_i hge
                have h8 : i3.val < 8 := by simp at hge; omega
                step as ⟨tmp, htmp⟩
                rw [htmp, getElem_eq_getElem! _ _ (by simp; omega), ← h2i3]
                exact hodd _ h8
          intro tmp htmp
          step with digit_point Q hQ pd tmp htmp as ⟨tmp1, htmp1⟩
          step with add_affine_spec _hr r1 tmp1 _ _ (hT _ _) (p256Laws.zpow_onCurve Q hQ _) hr1 htmp1 as ⟨r3, hr3⟩
          rw [p256Laws.twin_add_right p256G Q hGc hQ] at hr3
          exact hr3
        · rename_i hpe
          simp only [WP.spec_ok]
          have : pd.val = 0 := by simpa using hpe
          rw [this, add_zero]
          exact ⟨trivial, hr1⟩
      rintro ⟨m2, r2⟩ ⟨hm2, hr2⟩
      simp only at hm2 hr2 ⊢
      rw [hm2]
      have hie : it1.iter.end.val + 1 = it.iter.end.val := he1
      have hA' : nafVal (g.val.drop it1.iter.end.val) = gd.val + 2 * A := by
        rw [nafVal_drop _ _ (by omega), hie, hgd']
      have hB' : nafVal (p.val.drop it1.iter.end.val) = pd.val + 2 * B := by
        rw [nafVal_drop _ _ (by omega), hie, hpd']
      have hfin : ∀ r, jrep (twin p256G Q (2 * A + gd.val) (2 * B + pd.val)) r →
          it1.iter.start.val = 0 ∧ it1.iter.end.val ≤ 257 ∧
            jrep (twin p256G Q (nafVal (g.val.drop it1.iter.end.val)) (nafVal (p.val.drop it1.iter.end.val))) r ∧
            it1.iter.end.val < it.iter.end.val := by
        intro r hr
        refine ⟨by rw [hst]; exact hs, by omega, ?_, by omega⟩
        rw [hA', hB', add_comm (gd.val), add_comm (pd.val)]; exact hr
      split
      · rename_i hgne
        have hgv : gd.val ≠ 0 := by
          intro h
          have : gd = 0#i8 := (IScalar.eq_equiv _ _).mpr (by rw [h]; rfl)
          simp [this] at hgne
        have hdig := hg it1.iter.end.val hi
        rw [← hgd'] at hdig
        obtain ⟨hodd', hlt'⟩ := i8_natAbs gd 32 (by simp) hdig hgv
        step as ⟨i1, hi1⟩
        step with lookup_spec gm hgm.1 i1 (by rw [hi1]; omega) (by rw [hi1]; simp at hlt'; omega) as ⟨tmp, htmp⟩
        have htab0 := hgm.2 i1.val (by rw [hi1]; omega) (by rw [hi1]; simp at hlt'; omega)
        have hrep : p256Represents2 (p256Pow p256G gd.val.natAbs) (pairNat tmp.xy.val) := by
          rw [htmp, ← hi1]; exact htab0
        step with digit_point p256G hGc gd tmp hrep as ⟨tmp1, htmp1⟩
        step with add_affine_spec _hr r2 tmp1 _ _ (hT _ _) (p256Laws.zpow_onCurve p256G hGc _) hr2 htmp1 as
          ⟨r3, hr3⟩
        rw [p256Laws.twin_add_left p256G Q hGc hQ] at hr3
        have h := hfin r3 hr3
        exact h
      · rename_i hge
        have : gd.val = 0 := by simpa using hge
        have h := hfin r2 (by rw [this, add_zero]; exact hr2)
        show WP.spec (ok (ControlFlow.cont (it1, more, r2))) _
        rw [WP.spec_ok]
        exact ⟨h.1, h.2.1, rfl, h.2.2⟩
    · rw [ho]
      simp only [WP.spec_ok]
      have h0 : it.iter.end.val = 0 := by omega
      rwa [h0, List.drop_zero, List.drop_zero] at hres
  · exact ⟨hs, he, rfl, hres⟩

theorem twin_multiply_spec (_hr : Runs) (g p : mid.p256.Scalar) (Q : P256Point)
    (hQ : p256OnCurve Q) (odd : Std.Array mid.p256.AffineMontPoint 8#usize) (hodd : OddMultiples Q 1 odd)
    (more : Option (Std.Array mid.p256.AffineMontPoint 8#usize))
    (hmore : ∀ m, more = some m → OddMultiples Q 17 m) :
    mid.p256.JacobianMontPoint.public_twin_multiply g p odd more ⦃ r =>
      jrep (twin p256G Q (scNat g) (scNat p)) r ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_twin_multiply
  step with scalar_naf_spec 6#u32 (by simp) g as ⟨gd, hgv, hgd⟩
  apply WP.spec_bind (Pₘ := fun pd : Std.Array I8 257#usize => nafVal pd.val = scNat p ∧
    ∀ j < 257, nafDigit (if more = none then 16 else 32) (pd.val[j]!).val)
  · rcases more with _ | m
    · simp only
      apply WP.spec_mono (scalar_naf_spec 5#u32 (by simp) p)
      intro pd hpd; simpa using hpd
    · simp only
      apply WP.spec_mono (scalar_naf_spec 6#u32 (by simp) p)
      intro pd hpd; simpa using hpd
  intro pd ⟨hpv, hpd⟩
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index]
  step as ⟨a1, ha1⟩
  step*
  have hgl : gd.val.length = 257 := gd.property
  have hpl : pd.val.length = 257 := pd.property
  have hend : iter.iter.end.val = 257 := by rw [iter_post]; simp [s_post, Slice.len, hgl]
  have hgm : a1.to_slice.val = (mid.p256.precomp.CURVE_GENERATOR_PRECOMP.val[0]!).val := by
    rw [Array.val_to_slice, ha1, getElem_eq_getElem! _ _ (by simp)]
  have hrow : p256GRow a1.to_slice.val := by
    refine ⟨?_, hgm ▸ first_row⟩
    have hl := a1.property
    simp only [Array.val_to_slice] at hl ⊢
    rw [hl]
    simp
  apply WP.spec_mono (twin_loop_spec _hr Q hQ odd hodd more hmore gd pd hgd hpd a1.to_slice
    hrow iter (by rw [iter_post]; rfl)
    (by omega) result (by
      rw [hend, List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
      simp only [nafVal]
      rw [p256Laws.twin_zero p256G Q p256OnCurve_G hQ]; exact result_post))
  intro r hr
  rwa [hgv, hpv] at hr

/-! ## The x-coordinate check, `JacobianMontPoint::public_x_is` -/

theorem wordsNat_take_succ (l : List U64) (i : Nat) (hi : i < l.length) :
    wordsNat (l.take (i + 1)) = wordsNat (l.take i) + 2 ^ (64 * i) * (l[i]!).val := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, wordsNat, List.map_append,
    Nat.ofDigits_append, List.length_map, List.length_take, Nat.min_eq_left (by omega), ← wordsNat,
    getElem_eq_getElem! _ _ hi, ← pow_mul]
  simp []

theorem x_is_loop_spec (a : Std.Array U64 4#usize) (iter : core.ops.range.Range Usize)
    (rpn : Std.Array U64 4#usize) (carry : Bool) (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hinv : wordsNat (rpn.val.take iter.start.val) + 2 ^ (64 * iter.start.val) * carry.toNat =
      wordsNat (a.val.take iter.start.val) + wordsNat (mid.p256.CURVE_ORDER.val.take iter.start.val)) :
    mid.p256.JacobianMontPoint.public_x_is_loop iter a rpn carry ⦃ r =>
      wordsNat r.1.val + 2 ^ 256 * r.2.toNat = wordsNat a.val + n256 ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_x_is_loop
  have hal : a.val.length = 4 := a.property
  have hnl : mid.p256.CURVE_ORDER.val.length = 4 := mid.p256.CURVE_ORDER.property
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      wordsNat (x.2.1.val.take x.1.start.val) + 2 ^ (64 * x.1.start.val) * x.2.2.toNat =
        wordsNat (a.val.take x.1.start.val) + wordsNat (mid.p256.CURVE_ORDER.val.take x.1.start.val))
  · rintro ⟨it, r, c⟩ ⟨hs, he, hinv⟩
    simp only at hs he hinv ⊢
    unfold mid.p256.JacobianMontPoint.public_x_is_loop.body
    have hrl : r.val.length = 4 := r.property
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have h1 := core.num.U64.overflowing_add_eq i1 i2
      rcases hsc : core.num.U64.overflowing_add i1 i2 with ⟨s', c1⟩
      rw [hsc] at h1
      simp only [lift, bind_ok]
      have h2 := core.num.U64.overflowing_add_eq s' (core.convert.num.FromU64Bool.from c)
      rcases hsc2 : core.num.U64.overflowing_add s' (core.convert.num.FromU64Bool.from c) with ⟨s1, c2⟩
      rw [hsc2] at h2
      simp only at h1 h2
      change (do
        let a1 ← r.update it.start (core.num.U64.overflowing_add s' (core.convert.num.FromU64Bool.from c)).1
        ok (ControlFlow.cont (iter1, a1,
          c1 || (core.num.U64.overflowing_add s' (core.convert.num.FromU64Bool.from c)).2))) ⦃ _ ⦄
      rw [hsc2]
      dsimp only
      have hc : (core.convert.num.FromU64Bool.from c).val = c.toNat := by
        cases c <;> rfl
      simp only [hc] at h1 h2 ⊢
      have hsize : UScalar.size .U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
      have hmax : UScalar.max .U64 = 2 ^ 64 - 1 := by simp [U64.max_def, U64.numBits]
      have hsum : s1.val + 2 ^ 64 * (c1 || c2).toNat = i1.val + i2.val + c.toNat := by
        have hb1 := i1.hBounds; have hb2 := i2.hBounds; have hbs := s'.hBounds
        simp only [UScalarTy.numBits] at hb1 hb2 hbs
        rw [hsize, hmax] at h1 h2
        have hcv : c.toNat ≤ 1 := by cases c <;> decide
        generalize (2 : Nat) ^ 64 = M at *
        split_ifs at h1 with g1 <;> split_ifs at h2 with g2 <;> obtain ⟨e1, rfl⟩ := h1 <;>
          obtain ⟨e2, rfl⟩ := h2 <;> simp only [Bool.or_true, Bool.or_false, Bool.toNat_true,
            Bool.toNat_false] <;> omega
      step as ⟨a1, ha1⟩
      refine ⟨by omega, by rw [he1]; exact he, ?_, by omega⟩
      have hi4 : it.start.val < 4 := by omega
      have hal1 : (a1.val).length = 4 := a1.property
      have hset : a1.val = r.val.set it.start.val s1 := by rw [ha1, Std.Array.set_val_eq]
      rw [hst, wordsNat_take_succ _ _ (by omega), wordsNat_take_succ _ _ (by omega),
        wordsNat_take_succ _ _ (by omega)]
      have htk : a1.val.take it.start.val = r.val.take it.start.val := by
        rw [hset, List.take_set_of_le (by omega)]
      have hgi : (a1.val[it.start.val]!) = s1 := by
        rw [hset]; simp [hrl, hi4]
      rw [htk, hgi, ← getElem_eq_getElem! _ _ (by omega), ← getElem_eq_getElem! _ _ (by omega), ← hi1, ← hi2,
        show 64 * (it.start.val + 1) = 64 * it.start.val + 64 by ring, pow_add]
      have e : 2 ^ (64 * it.start.val) * s1.val + 2 ^ (64 * it.start.val) * 2 ^ 64 * (c1 || c2).toNat =
          2 ^ (64 * it.start.val) * (i1.val + i2.val + c.toNat) := by rw [← hsum]; ring
      linear_combination e + hinv
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have h4 : it.start.val = 4 := by omega
      rw [h4, List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega), CURVE_ORDER_val] at hinv
      exact hinv
  · exact ⟨hs, he, hinv⟩

theorem dec_tomont (v : Nat) : dec (2 ^ 256 * v % p256) = v := by
  simp only [dec, cast_mod_p, Nat.cast_mul]
  rw [← mul_assoc, mul_comm (p256RInv : ZMod p256), R_mul_RInv, one_mul]

theorem x_is_closure_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (z2 : mid.p256.FieldElement) (x : Nat)
    (hx : x < p256) (hX : (tripleNat pt.xyz.val).1 < p256) (hz2 : feNat z2 < p256)
    (heq : ∀ v : Nat, dec (feNat z2) * v = dec (tripleNat pt.xyz.val).1 ↔ (v : ZMod p256) = x)
    (v : Std.Array U64 4#usize) :
    mid.p256.JacobianMontPoint.public_x_is.closure.Insts.CoreOpsFunctionFnTupleArrayU644Bool.call (z2, pt) v
      ⦃ b => b ↔ wordsNat v.val % p256 = x ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_x_is.closure.Insts.CoreOpsFunctionFnTupleArrayU644Bool.call
  step with as_mont_spec _hr v as ⟨fe1, hfe1⟩
  step with mont_mul_spec _hr fe1 z2 (by rw [hfe1]; exact Nat.mod_lt _ p256_pos) hz2 as ⟨fe2, hfe2⟩
  step as ⟨fe3, hfe3⟩
  have hfe3X : feNat fe3 = (tripleNat pt.xyz.val).1 := by simp [tripleNat, feNat, hfe3]
  step as ⟨b, hb⟩
  rw [hb, hfe3X, eq_of_dec _ _ (by rw [hfe2]; exact Nat.mod_lt _ p256_pos) hX, hfe2, dec_mont_mul, hfe1,
    dec_tomont, mul_comm, heq, ← cast_mod_p, ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.mod_eq_of_lt hx]

theorem p256_lt_two_n : p256 < 2 * n256 := by unfold p256 n256; decide
theorem n256_lt_p256 : n256 < p256 := by unfold p256 n256; decide

theorem x_is_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (x y : Nat) (h : jrep (some (x, y)) pt)
    (r : mid.p256.Scalar) (hr : scNat r < n256) :
    mid.p256.JacobianMontPoint.public_x_is pt r ⦃ b => b ↔ x % n256 = scNat r ⦄ := by
  obtain ⟨hX, hY, hZ, hP⟩ := h
  rw [ofJacobian_dec] at hP
  set X := (tripleNat pt.xyz.val).1
  set Z := (tripleNat pt.xyz.val).2.2
  have hZ0 : dec Z ≠ 0 := fun h0 => by rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)] at hP; cases hP
  rw [ite_eq_right_iff.mpr (fun h => absurd h hZ0)] at hP
  simp only [Option.some.injEq, Prod.mk.injEq] at hP
  obtain ⟨hxv, -⟩ := hP
  have hx : x < p256 := by rw [← hxv]; exact ZMod.val_lt _
  unfold mid.p256.JacobianMontPoint.public_x_is
  step as ⟨fz, hfz⟩
  have hfzZ : feNat fz = Z := by simp [Z, tripleNat, feNat, hfz]
  step with mont_sqr_spec _hr fz (by rw [hfzZ]; exact hZ) as ⟨z2, hz2⟩
  have hz2p : feNat z2 < p256 := by rw [hz2]; exact Nat.mod_lt _ p256_pos
  have heq : ∀ v : Nat, dec (feNat z2) * v = dec X ↔ (v : ZMod p256) = x := by
    intro v
    rw [hz2, dec_mont_sqr, hfzZ, ← hxv, ZMod.natCast_val, ZMod.cast_id', id,
      eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hZ0), mul_comm]
  have hrp : scNat r < p256 := lt_trans hr n256_lt_p256
  have hp2n := p256_lt_two_n
  have hmod : x % n256 = scNat r ↔ x = scNat r ∨ x = scNat r + n256 := by
    constructor
    · intro h
      by_cases hxn : x < n256
      · left; rw [← h, Nat.mod_eq_of_lt hxn]
      · right; rw [← h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rintro (rfl | rfl)
      · exact Nat.mod_eq_of_lt hr
      · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  step with x_is_closure_spec _hr pt z2 x hx hX hz2p heq r as ⟨b, hb⟩
  rw [show wordsNat r.val % p256 = scNat r from Nat.mod_eq_of_lt hrp] at hb
  rw [hmod]
  split
  · rename_i hbt
    simp only [WP.spec_ok, true_iff]
    exact Or.inl (hb.mp hbt).symm
  · rename_i hbf
    have hxr : x ≠ scNat r := fun h => hbf (hb.mpr h.symm)
    step with x_is_loop_spec r { start := 0#usize, «end» := 4#usize } (Array.repeat 4#usize 0#u64) false
      (by simp) (by simp) (by simp [wordsNat]) as ⟨rpn, carry, hrpn⟩
    split
    · rename_i hc
      simp only [hc, Bool.toNat_true, Nat.mul_one] at hrpn
      rw [WP.spec_ok]
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rintro (h | h)
      · exact absurd h hxr
      · have hp := p256_lt
        simp only [scNat] at h hrpn
        generalize (2 : Nat) ^ 256 = M at *
        omega
    · rename_i hc
      simp only [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hrpn
      step with below_p_spec rpn as ⟨b1, hb1⟩
      rw [hrpn] at hb1
      split
      · rename_i hb1t
        have hlt := hb1.mp hb1t
        step with x_is_closure_spec _hr pt z2 x hx hX hz2p heq rpn as ⟨b2, hb2⟩
        rw [hrpn, Nat.mod_eq_of_lt hlt] at hb2
        rw [hb2]
        constructor
        · intro h; exact Or.inr h.symm
        · rintro (h | h)
          · exact absurd h hxr
          · exact h.symm
      · rename_i hb1f
        rw [WP.spec_ok]
        refine ⟨fun h => absurd h (by simp), ?_⟩
        rintro (h | h)
        · exact absurd h hxr
        · simp only [scNat] at h hrpn ⊢
          exact absurd (hb1.mpr (by omega)) hb1f

/-! ## Affine conversion, `JacobianMontPoint::public_batch_as_affine` -/

/-- A finite point's Jacobian coordinates, as their values: z is nonzero and
the point is (x/z², y/z³). -/
theorem jrep_some (P : P256Point) (pt : mid.p256.JacobianMontPoint) (h : jrep P pt) (hne : P ≠ none) :
    (tripleNat pt.xyz.val).1 < p256 ∧ (tripleNat pt.xyz.val).2.1 < p256 ∧ (tripleNat pt.xyz.val).2.2 < p256 ∧
      dec (tripleNat pt.xyz.val).2.2 ≠ 0 ∧
      P = some ((dec (tripleNat pt.xyz.val).1 * (dec (tripleNat pt.xyz.val).2.2 ^ 2)⁻¹).val,
        (dec (tripleNat pt.xyz.val).2.1 * (dec (tripleNat pt.xyz.val).2.2 ^ 3)⁻¹).val) := by
  obtain ⟨hX, hY, hZ, hP⟩ := h
  rw [ofJacobian_dec] at hP
  have hZ0 : dec (tripleNat pt.xyz.val).2.2 ≠ 0 := fun h0 => by
    rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)] at hP; exact hne hP.symm
  rw [ite_eq_right_iff.mpr (fun h => absurd h hZ0)] at hP
  exact ⟨hX, hY, hZ, hZ0, hP.symm⟩

theorem as_affine_by_spec (_hr : Runs) (pt : mid.p256.JacobianMontPoint) (P : P256Point) (h : jrep P pt) (hne : P ≠ none)
    (zi : mid.p256.FieldElement) (hzi : feNat zi < p256)
    (hinv : dec (feNat zi) = (dec (tripleNat pt.xyz.val).2.2)⁻¹) :
    mid.p256.JacobianMontPoint.as_affine_by pt zi ⦃ a => p256Represents2 P (pairNat a.xy.val) ⦄ := by
  obtain ⟨hX, hY, hZ, hZ0, rfl⟩ := jrep_some P pt h hne
  have hlt : ∀ x, x % p256 < p256 := fun x => Nat.mod_lt _ p256_pos
  unfold mid.p256.JacobianMontPoint.as_affine_by
  step with mont_sqr_spec _hr zi hzi as ⟨z2, hz2⟩
  step with mont_mul_spec _hr z2 zi (by rw [hz2]; exact hlt _) hzi as ⟨z3, hz3⟩
  step as ⟨fx, hfx⟩
  have hfxX : feNat fx = (tripleNat pt.xyz.val).1 := by simp [tripleNat, feNat, hfx]
  step with mont_mul_spec _hr fx z2 (by rw [hfxX]; exact hX) (by rw [hz2]; exact hlt _) as ⟨x, hx⟩
  step as ⟨fy, hfy⟩
  have hfyY : feNat fy = (tripleNat pt.xyz.val).2.1 := by simp [tripleNat, feNat, hfy]
  step with mont_mul_spec _hr fy z3 (by rw [hfyY]; exact hY) (by rw [hz3]; exact hlt _) as ⟨y, hy⟩
  step as ⟨a, ha⟩
  rw [ha, pairNat_append _ _ x.property y.property]
  refine ⟨by rw [show wordsNat x.val = feNat x from rfl, hx]; exact hlt _,
    by rw [show wordsNat y.val = feNat y from rfl, hy]; exact hlt _, ?_⟩
  rw [show wordsNat x.val = feNat x from rfl, show wordsNat y.val = feNat y from rfl, val_dec, val_dec, hx, hy,
    dec_mont_mul, dec_mont_mul, hz3, hz2, dec_mont_mul, dec_mont_sqr, hinv, hfxX, hfyY]
  congr 3 <;> field_simp

instance : Inhabited mid.p256.JacobianMontPoint := ⟨⟨Array.repeat 12#usize 0#u64⟩⟩

/-- The value of the z of point `j`. -/
abbrev zv (pts : Std.Array mid.p256.JacobianMontPoint 8#usize) (j : Nat) : ZMod p256 :=
  dec (tripleNat (pts.val[j]!).xyz.val).2.2

theorem batch_loop0_spec (_hr : Runs) (pts : Std.Array mid.p256.JacobianMontPoint 8#usize)
    (hz : ∀ j < 8, (tripleNat (pts.val[j]!).xyz.val).2.2 < p256)
    (iter : core.ops.range.Range Usize) (pre : Std.Array mid.p256.FieldElement 8#usize)
    (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8) (he : iter.end.val = 8)
    (hpre : ∀ j < iter.start.val, feNat (pre.val[j]!) < p256 ∧ dec (feNat (pre.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t) :
    mid.p256.JacobianMontPoint.public_batch_as_affine_loop0 iter pts pre ⦃ r =>
      ∀ j < 8, feNat (r.val[j]!) < p256 ∧ dec (feNat (r.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_batch_as_affine_loop0
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧ x.1.end.val = 8 ∧
      ∀ j < x.1.start.val, feNat (x.2.val[j]!) < p256 ∧ dec (feNat (x.2.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t)
  · rintro ⟨it, pr⟩ ⟨hs1, hs, he, hpr⟩
    simp only at hs1 hs he hpr ⊢
    unfold mid.p256.JacobianMontPoint.public_batch_as_affine_loop0.body
    have hprl : pr.val.length = 8 := pr.property
    have hptl : pts.val.length = 8 := pts.property
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨fe, hfe⟩
      step as ⟨jmp, hjmp⟩
      step as ⟨fz, hfz⟩
      have hfe' : fe = pr.val[it.start.val - 1]! := by rw [hfe, getElem_eq_getElem! _ _ (by omega), hi1]
      have hjmp' : jmp = pts.val[it.start.val - 1]! := by rw [hjmp, getElem_eq_getElem! _ _ (by omega), hi1]
      have hfzv : feNat fz = (tripleNat (pts.val[it.start.val - 1]!).xyz.val).2.2 := by
        rw [← hjmp']; simp [tripleNat, feNat, hfz]
      obtain ⟨hfelt, hfev⟩ := hpr (it.start.val - 1) (by omega)
      rw [← hfe'] at hfelt hfev
      step with mont_mul_spec _hr fe fz hfelt (by rw [hfzv]; exact hz _ (by omega)) as ⟨fe2, hfe2⟩
      step as ⟨a, ha⟩
      refine ⟨by omega, by omega, by rw [he1]; exact he, ?_, by omega⟩
      intro j hj
      have hav : a.val = pr.val.set it.start.val fe2 := by rw [ha, Std.Array.set_val_eq]
      by_cases hji : j = it.start.val
      · subst hji
        have : a.val[it.start.val]! = fe2 := by
          rw [hav]; simp [hprl, show it.start.val < 8 by omega]
        rw [this, hfe2]
        refine ⟨Nat.mod_lt _ p256_pos, ?_⟩
        rw [dec_mont_mul, hfev, hfzv, show it.start.val = (it.start.val - 1) + 1 by omega,
          Finset.prod_range_succ]
        simp
      · have : a.val[j]! = pr.val[j]! := by
          rw [hav]; simp [List.getElem!_eq_getElem?_getD, Ne.symm hji]
        rw [this]; exact hpr j (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      intro j hj; exact hpr j (by omega)
  · exact ⟨hs1, hs, he, hpre⟩

theorem zv_ne_zero (pts : Std.Array mid.p256.JacobianMontPoint 8#usize) (Ps : Nat → P256Point)
    (h : ∀ j < 8, jrep (Ps j) (pts.val[j]!) ∧ Ps j ≠ none) (j : Nat) (hj : j < 8) : zv pts j ≠ 0 :=
  (jrep_some _ _ (h j hj).1 (h j hj).2).2.2.2.1

theorem batch_loop1_spec (_hr : Runs) (pts : Std.Array mid.p256.JacobianMontPoint 8#usize) (Ps : Nat → P256Point)
    (h : ∀ j < 8, jrep (Ps j) (pts.val[j]!) ∧ Ps j ≠ none) (pre : Std.Array mid.p256.FieldElement 8#usize)
    (hpre : ∀ j < 8, feNat (pre.val[j]!) < p256 ∧ dec (feNat (pre.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (hs : iter.iter.start.val = 0)
    (he : iter.iter.end.val ≤ 8) (inv : mid.p256.FieldElement)
    (hinv : feNat inv < p256 ∧ dec (feNat inv) = (∏ t ∈ Finset.range iter.iter.end.val, zv pts t)⁻¹)
    (r : Std.Array mid.p256.AffineMontPoint 8#usize)
    (hr : ∀ j, iter.iter.end.val ≤ j → j < 8 → p256Represents2 (Ps j) (pairNat (r.val[j]!).xy.val)) :
    mid.p256.JacobianMontPoint.public_batch_as_affine_loop1 iter pts pre inv r ⦃ r' =>
      ∀ j < 8, p256Represents2 (Ps j) (pairNat (r'.val[j]!).xy.val) ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_batch_as_affine_loop1
  have hlt : ∀ x, x % p256 < p256 := fun x => Nat.mod_lt _ p256_pos
  apply loop.spec_decr_nat (fun x => x.1.iter.end.val)
    (fun x => x.1.iter.start.val = 0 ∧ x.1.iter.end.val ≤ 8 ∧
      (feNat x.2.1 < p256 ∧ dec (feNat x.2.1) = (∏ t ∈ Finset.range x.1.iter.end.val, zv pts t)⁻¹) ∧
      ∀ j, x.1.iter.end.val ≤ j → j < 8 → p256Represents2 (Ps j) (pairNat (x.2.2.val[j]!).xy.val))
  · rintro ⟨it, iv, rr⟩ ⟨hs, he, ⟨hivl, hiv⟩, hrr⟩
    simp only at hs he hivl hiv hrr ⊢
    unfold mid.p256.JacobianMontPoint.public_batch_as_affine_loop1.body
    have hrl : rr.val.length = 8 := rr.property
    have hptl : pts.val.length = 8 := pts.property
    have hprl : pre.val.length = 8 := pre.property
    step as ⟨o, it1, hst, ho⟩
    split_ifs at ho with hlt'
    · obtain ⟨rfl, he1⟩ := ho
      simp only
      set i := it1.iter.end.val
      have hi8 : i < 8 := by omega
      step as ⟨jmp, hjmp⟩
      step as ⟨fe, hfe⟩
      have hjmp' : jmp = pts.val[i]! := by rw [hjmp, getElem_eq_getElem! _ _ (by omega)]
      have hfe' : fe = pre.val[i]! := by rw [hfe, getElem_eq_getElem! _ _ (by omega)]
      obtain ⟨hfel, hfev⟩ := hpre i hi8
      rw [← hfe'] at hfel hfev
      step with mont_mul_spec _hr iv fe hivl hfel as ⟨fe1, hfe1⟩
      have hzi : dec (feNat fe1) = (dec (tripleNat jmp.xyz.val).2.2)⁻¹ := by
        rw [hfe1, dec_mont_mul, hiv, hfev, ← he1, Finset.prod_range_succ, hjmp']
        have := zv_ne_zero pts Ps h i hi8
        have hp : ∏ t ∈ Finset.range i, zv pts t ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun t ht => zv_ne_zero pts Ps h t (by simp at ht; omega)
        field_simp
      obtain ⟨hj1, hj2⟩ := h i hi8
      rw [← hjmp'] at hj1
      step with as_affine_by_spec _hr jmp (Ps i) hj1 hj2 fe1 (by rw [hfe1]; exact hlt _) hzi as ⟨amp, hamp⟩
      step as ⟨a, ha⟩
      step as ⟨fz, hfz⟩
      have hfzv : feNat fz = (tripleNat jmp.xyz.val).2.2 := by simp [tripleNat, feNat, hfz]
      have hzl : feNat fz < p256 := by rw [hfzv]; exact (jrep_some _ _ hj1 hj2).2.2.1
      step with mont_mul_spec _hr iv fz hivl hzl as ⟨iv1, hiv1⟩
      have hiv1v : dec (feNat iv1) = (∏ t ∈ Finset.range i, zv pts t)⁻¹ := by
        rw [hiv1, dec_mont_mul, hiv, hfzv, ← he1, Finset.prod_range_succ, hjmp']
        have := zv_ne_zero pts Ps h i hi8
        have hp : ∏ t ∈ Finset.range i, zv pts t ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun t ht => zv_ne_zero pts Ps h t (by simp at ht; omega)
        field_simp
        try exact div_self this
      have hfin : ∀ j, i ≤ j → j < 8 → p256Represents2 (Ps j) (pairNat (a.val[j]!).xy.val) := by
        have hav : a.val = rr.val.set i amp := by rw [ha, Std.Array.set_val_eq]
        intro j hj1' hj8
        by_cases hji : j = i
        · rw [hji]
          have : a.val[i]! = amp := by
            rw [hav]; simp [hrl, hi8]
          rw [this]; exact hamp
        · have : a.val[j]! = rr.val[j]! := by
            rw [hav]; simp [List.getElem!_eq_getElem?_getD, Ne.symm hji]
          rw [this]; exact hrr j (by omega) hj8
      have hit1 : it1.iter.start.val = 0 := by rw [hst]; exact hs
      have hiv1l : feNat iv1 < p256 := by rw [hiv1]; exact hlt _
      exact ⟨hit1, by omega, hiv1l, hiv1v, hfin, by omega⟩
    · rw [ho]
      simp only [WP.spec_ok]
      intro j hj; exact hrr j (by omega) hj
  · exact ⟨hs, he, hinv, hr⟩

theorem batch_spec (_hr : Runs) (pts : Std.Array mid.p256.JacobianMontPoint 8#usize) (Ps : Nat → P256Point)
    (h : ∀ j < 8, jrep (Ps j) (pts.val[j]!) ∧ Ps j ≠ none) :
    mid.p256.JacobianMontPoint.public_batch_as_affine pts ⦃ r =>
      ∀ j < 8, p256Represents2 (Ps j) (pairNat (r.val[j]!).xy.val) ⦄ := by
  unfold mid.p256.JacobianMontPoint.public_batch_as_affine
  have hlt : ∀ x, x % p256 < p256 := fun x => Nat.mod_lt _ p256_pos
  have hptl : pts.val.length = 8 := pts.property
  have hz : ∀ j < 8, (tripleNat (pts.val[j]!).xyz.val).2.2 < p256 := fun j hj => (h j hj).1.2.2.1
  step as ⟨sl, hsl⟩
  step with batch_loop0_spec _hr pts hz { start := 1#usize, «end» := Slice.len sl }
    (Array.repeat 8#usize mid.p256.CURVE_ONE_MONT) (by simp) (by simp) (by simp [hsl, Slice.len])
    (by
      intro j hj
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      have : (Array.repeat 8#usize mid.p256.CURVE_ONE_MONT).val[0]! = mid.p256.CURVE_ONE_MONT := by
        simp [Array.repeat]
      rw [this, CURVE_ONE_MONT_val, dec_one]
      exact ⟨hlt _, by simp⟩) as ⟨pre, hpre⟩
  step as ⟨fe, hfe⟩
  step as ⟨jmp, hjmp⟩
  step as ⟨fz, hfz⟩
  have hfe' : fe = pre.val[7]! := by rw [hfe, getElem_eq_getElem! _ _ (by simp)]
  have hjmp' : jmp = pts.val[7]! := by rw [hjmp, getElem_eq_getElem! _ _ (by simp)]
  have hfzv : feNat fz = (tripleNat (pts.val[7]!).xyz.val).2.2 := by rw [← hjmp']; simp [tripleNat, feNat, hfz]
  obtain ⟨hfel, hfev⟩ := hpre 7 (by norm_num)
  rw [← hfe'] at hfel hfev
  step with mont_mul_spec _hr fe fz hfel (by rw [hfzv]; exact hz 7 (by norm_num)) as ⟨pr, hpr⟩
  have hprv : dec (feNat pr) = ∏ t ∈ Finset.range 8, zv pts t := by
    rw [hpr, dec_mont_mul, hfev, hfzv, Finset.prod_range_succ (fun t => zv pts t) 7]
  have hp8 : ∏ t ∈ Finset.range 8, zv pts t ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun t ht => zv_ne_zero pts Ps h t (by simp at ht; omega)
  step with demont_spec _hr pr (by rw [hpr]; exact hlt _) as ⟨f2, hf2⟩
  have hf2v : ((feNat f2 : Nat) : ZMod p256) = ∏ t ∈ Finset.range 8, zv pts t := by
    rw [hf2, cast_mod_p, ← hprv]; push_cast; rfl
  step as ⟨f3, hf3l, hf3, _⟩
  have hf2nz : feNat f2 % p256 ≠ 0 := by
    intro h0; apply hp8; rw [← hf2v, ← cast_mod_p, h0]; simp
  have hf3v : ((feNat f3 : Nat) : ZMod p256) = (∏ t ∈ Finset.range 8, zv pts t)⁻¹ := by
    have := congrArg (fun x : Nat => (x : ZMod p256)) (hf3 hf2nz)
    simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at this
    rw [← hf2v]; exact (inv_eq_of_mul_eq_one_right this).symm
  step with as_mont_spec _hr f3 as ⟨iv, hiv⟩
  simp only [mid.p256.AffineMontPoint.Insts.CoreDefaultDefault.default, core.default.DefaultArray.default,
    ]
  step as ⟨sl1, hsl1⟩
  step as ⟨it, hit⟩
  apply batch_loop1_spec _hr pts Ps h pre hpre it (by rw [hit]; rfl) (by rw [hit]; simp [hsl1, Slice.len])
    iv ⟨by rw [hiv]; exact hlt _, by rw [hiv, dec_tomont, hf3v, hit]; simp [hsl1, Slice.len]⟩
  intro j hj; rw [hit] at hj; simp [hsl1, Slice.len] at hj; omega

/-! ## A key's odd multiples, `AffineMontPoint::public_odd_multiples` -/

theorem n256_big : 64 < n256 := by unfold n256; decide

theorem odd_loop_spec (_hr : Runs) (Q : P256Point) (hQ : p256OnCurve Q) (hQo : P256OrderOf Q)
    (p2 : mid.p256.JacobianMontPoint) (hp2 : jrep (p256ZPow Q 2) p2) (iter : core.ops.range.Range Usize)
    (m : Std.Array mid.p256.JacobianMontPoint 8#usize) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8)
    (he : iter.end.val = 8) (hm : ∀ j : Nat, j < iter.start.val → jrep (p256ZPow Q (2 * (j : Int) + 1)) (m.val[j]!)) :
    mid.p256.AffineMontPoint.public_odd_multiples_loop iter p2 m ⦃ r =>
      ∀ j : Nat, j < 8 → jrep (p256ZPow Q (2 * (j : Int) + 1)) (r.val[j]!) ⦄ := by
  unfold mid.p256.AffineMontPoint.public_odd_multiples_loop
  have hn := n256_big
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧ x.1.end.val = 8 ∧
      ∀ j : Nat, j < x.1.start.val → jrep (p256ZPow Q (2 * (j : Int) + 1)) (x.2.val[j]!))
  · rintro ⟨it, mm⟩ ⟨hs1, hs, he, hmm⟩
    simp only at hs1 hs he hmm ⊢
    unfold mid.p256.AffineMontPoint.public_odd_multiples_loop.body
    have hml : mm.val.length = 8 := mm.property
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step as ⟨i1, hi1⟩
      step as ⟨jmp, hjmp⟩
      have hjmp' : jmp = mm.val[it.start.val - 1]! := by rw [hjmp, getElem_eq_getElem! _ _ (by omega), hi1]
      have hj := hmm (it.start.val - 1) (by omega)
      rw [← hjmp'] at hj
      step with jac_add_spec _hr jmp p2 _ _ hj hp2 (fun h => absurd h (p256Laws.zpow_ne Q hQ hQo _ _
        (by omega) (by omega))) as ⟨s1, hs1'⟩
      rw [p256Laws.mul_zpow Q hQ] at hs1'
      step as ⟨a, ha⟩
      refine ⟨by omega, by omega, by rw [he1]; exact he, ?_, by omega⟩
      have hav : a.val = mm.val.set it.start.val s1 := by rw [ha, Std.Array.set_val_eq]
      intro j hj'
      by_cases hji : j = it.start.val
      · rw [hji]
        have : a.val[it.start.val]! = s1 := by
          rw [hav]; simp [hml, show it.start.val < 8 by omega]
        rw [this]
        have e : (2 * ((it.start.val - 1 : Nat) : Int) + 1 + 2) = 2 * (it.start.val : Int) + 1 := by omega
        rwa [e] at hs1'
      · have : a.val[j]! = mm.val[j]! := by
          rw [hav]; simp [List.getElem!_eq_getElem?_getD, Ne.symm hji]
        rw [this]; exact hmm j (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      intro j hj; exact hmm j (by omega)
  · exact ⟨hs1, hs, he, hm⟩

theorem odd_multiples_spec (_hr : Runs) (pt : mid.p256.AffineMontPoint) (Q : P256Point)
    (hQ : p256OnCurve Q) (hQo : P256OrderOf Q) (h : p256Represents2 Q (pairNat pt.xy.val)) :
    mid.p256.AffineMontPoint.public_odd_multiples pt ⦃ m => OddMultiples Q 1 m ⦄ := by
  unfold mid.p256.AffineMontPoint.public_odd_multiples
  have hn := n256_big
  step with from_affine_spec pt Q h as ⟨p, hp⟩
  step with double_spec _hr p Q hp as ⟨p2, hp2⟩
  have hQ1 := p256Laws.zpow_one Q hQ
  rw [← hQ1, p256Laws.mul_zpow Q hQ] at hp2
  rw [← hQ1] at hp
  step as ⟨sl, hsl⟩
  step with odd_loop_spec _hr Q hQ hQo p2 hp2 { start := 1#usize, «end» := Slice.len sl }
    (Array.repeat 8#usize p) (by simp) (by simp) (by simp [hsl, Slice.len])
    (by
      intro j hj
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      have : (Array.repeat 8#usize p).val[0]! = p := by simp [Array.repeat]
      rw [this]; simpa using hp) as ⟨m, hm⟩
  apply WP.spec_mono (batch_spec _hr m (fun j => p256ZPow Q (2 * j + 1))
    (fun j hj => ⟨hm j hj, p256Laws.zpow_ne_none Q hQ hQo _ (by omega) (by omega)⟩))
  intro r hr j hj
  have := hr j hj
  rwa [show (2 * (j : Int) + 1) = ((2 * j + 1 : Nat) : Int) by push_cast; ring, P256Laws.zpow_natCast] at this

/-- `<[T; N]>::map`'s fold, for a step that keeps the closure: each element
goes to its image, after `acc`. -/
theorem map_fold_spec {T F U : Type} [Inhabited T] [Inhabited U] (g : List U × F → T → Result (List U × F))
    (f : F) (P : T → U → Prop) (l : List T)
    (hg : ∀ x ∈ l, ∀ acc, g (acc, f) x ⦃ r => ∃ y, r = (acc ++ [y], f) ∧ P x y ⦄) (acc : List U) :
    l.foldlM g (acc, f) ⦃ res =>
      res.1.length = acc.length + l.length ∧ res.1.take acc.length = acc ∧
        ∀ i < l.length, P l[i]! res.1[acc.length + i]! ⦄ := by
  induction l generalizing acc with
  | nil =>
    show (ok (acc, f) : Result _) ⦃ _ ⦄
    simp [WP.spec_ok]
  | cons x xs ih =>
    show Std.bind (g (acc, f) x) (fun s => List.foldlM g s xs) ⦃ _ ⦄
    apply WP.spec_bind (hg x (by simp) acc)
    rintro _ ⟨y, rfl, hP⟩
    apply WP.spec_mono (ih (fun z hz => hg z (by simp [hz])) (acc ++ [y]))
    rintro ⟨r, _⟩ ⟨hl, ht, hall⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hl ht hall ⊢
    have hres : r = acc ++ y :: r.drop (acc.length + 1) := by
      conv_lhs => rw [← List.take_append_drop (acc.length + 1) r, ht]
      simp
    refine ⟨by omega, ?_, ?_⟩
    · rw [hres]; simp
    · intro i hi
      cases i with
      | zero =>
        have : r[acc.length]! = y := by rw [hres]; simp
        simpa [this] using hP
      | succ i =>
        have := hall i (by omega)
        simpa [show acc.length + 1 + i = acc.length + (i + 1) by omega] using this

/-- `<[T; N]>::map`, for a closure that keeps its state. -/
theorem map_spec {T F U : Type} [Inhabited T] [Inhabited U] {N : Usize} (inst : core.ops.function.FnMut F T U)
    (a : Std.Array T N) (f : F) (P : T → U → Prop)
    (h : ∀ x ∈ a.val, inst.call_mut f x ⦃ r => P x r.1 ∧ r.2 = f ⦄) :
    core.array.Array.map inst a f ⦃ r => ∀ i < N.val, P a.val[i]! r.val[i]! ⦄ := by
  unfold core.array.Array.map
  have hf := map_fold_spec (fun (acc, f) x => do
    let (y, f) ← inst.call_mut f x
    ok (acc ++ [y], f)) f P a.val (fun x hx acc => by
      simp only
      step with h x hx as ⟨y, g, hy, hg⟩
      exact ⟨y, rfl, hg, hy⟩) []
  apply WP.spec_bind hf
  rintro ⟨l, g⟩ ⟨hl, -, hall⟩
  replace hl : l.length = a.val.length := by simpa using hl
  replace hall : ∀ i < a.val.length, P a.val[i]! l[i]! := by simpa using hall
  show (if h : l.length = N.val then ok (Array.from l h) else fail Error.panic) ⦃ _ ⦄
  have hl' : l.length = N.val := by rw [hl]; exact a.property
  simp only [dite_eq_left hl', WP.spec_ok]
  intro i hi
  have := hall i (by rw [a.property]; exact hi)
  simpa [Array.from_val] using this

/-- The odd multiples a key's cache builds: 17Q to 31Q, from its Q to 15Q. -/
theorem more_odd_spec (_hr : Runs) (Q : P256Point) (hQ : p256OnCurve Q) (hQo : P256OrderOf Q)
    (odd : Std.Array mid.p256.AffineMontPoint 8#usize) (hodd : OddMultiples Q 1 odd) :
    mid.p256.AffineMontPoint.public_more_odd_multiples odd ⦃ m => OddMultiples Q 17 m ⦄ := by
  unfold mid.p256.AffineMontPoint.public_more_odd_multiples
  have hn := n256_big
  have hol : odd.val.length = 8 := odd.property
  have hz : ∀ k : Nat, p256Pow Q k = p256ZPow Q k := fun k => (P256Laws.zpow_natCast Q k).symm
  step as ⟨a7, ha7⟩
  have h7 := hodd 7 (by norm_num)
  rw [← getElem_eq_getElem! _ _ (by omega), ← ha7, hz] at h7
  step with from_affine_spec a7 _ h7 as ⟨p16, hp16⟩
  step as ⟨a0, ha0⟩
  have h0 := hodd 0 (by norm_num)
  rw [← getElem_eq_getElem! _ _ (by omega), ← ha0, hz] at h0
  step with add_inplace_affine_spec _hr p16 a0 _ _ hp16 h0
    (p256Laws.zpow_ne Q hQ hQo _ _ (by norm_num) (by norm_num; omega)) as ⟨p161, hp161⟩
  rw [p256Laws.mul_zpow Q hQ] at hp161
  have hadd : ∀ x, mid.p256.JacobianMontPoint.add_inplace_affine p161 x ⦃ r =>
      ∀ k : Nat, 1 ≤ k → k ≤ 15 → p256Represents2 (p256ZPow Q k) (pairNat x.xy.val) →
        jrep (p256ZPow Q (16 + k)) r ⦄ := by
    intro x
    unfold mid.p256.JacobianMontPoint.add_inplace_affine
    step as ⟨inf, hinf⟩
    step as ⟨a, ha⟩
    intro k hk1 hk15 hrep
    have := ha _ _ hp161 hrep (p256Laws.zpow_ne Q hQ hQo _ _ (by omega) (by omega))
    rw [p256Laws.mul_zpow Q hQ] at this
    exact this
  step with map_spec
    mid.p256.AffineMontPoint.public_more_odd_multiples.closure.Insts.CoreOpsFunctionFnMutTupleAffineMontPointJacobianMontPoint
    odd p161 (fun x r => ∀ k : Nat, 1 ≤ k → k ≤ 15 → p256Represents2 (p256ZPow Q k) (pairNat x.xy.val) →
      jrep (p256ZPow Q (16 + k)) r) (fun x _ => by
    simp only [mid.p256.AffineMontPoint.public_more_odd_multiples.closure.Insts.CoreOpsFunctionFnMutTupleAffineMontPointJacobianMontPoint.call_mut]
    step with hadd x as ⟨r, hr⟩
    exact hr) as ⟨l, hl⟩
  apply WP.spec_mono (batch_spec _hr l (fun j => p256ZPow Q (16 + (2 * j + 1))) (by
    intro j hj
    refine ⟨?_, p256Laws.zpow_ne_none Q hQ hQo _ (by omega) (by omega)⟩
    have hj' := hodd j hj
    rw [hz] at hj'
    exact hl j (by simpa using hj) (2 * j + 1) (by omega) (by omega) (by push_cast at hj' ⊢; exact hj')))
  intro r hr j hj
  have := hr j hj
  rwa [show (16 + (2 * (j : Int) + 1)) = ((2 * j + 17 : Nat) : Int) by push_cast; ring, ← hz] at this

/-! ## Raw verification, `VerifyingKey::raw_ecdsa_verify` -/

end P256

/-- rind's debug-only check that an operation holds its entry guard passes,
as every caller holds one; release builds compile it out. -/
def Held : Prop := low.entry.Entry.assert_held = ok ()

/-- A verifying key's caches of P, ..., 15P and 17P, ..., 31P, and a signing
key's cache of its encoded public key, whose atomics Aeneas cannot translate:
`ReuseCache::new` returns a cache, each cache holds only what its build
returns, built from the key's own point or scalar, which never changes after
the key is made, so whatever every such build's value satisfies,
`get_or_build_now`'s value does, and `get_or_build`'s, unless `None`, and a
clone, which copies a built value, returns. `get_or_build_now` on a signing
key's cache returns, whatever its build, if that build does: x86_64's key
check stores an encoding it has checked, `Rind.X86_64.P256KeyCheck`. -/
structure Cached : Prop where
  new : ∃ c, low.generic.reuse_cache.ReuseCache.new
      (Array.Insts.CoreMarkerCopy 8#usize mid.p256.AffineMontPoint.Insts.CoreMarkerCopy)
      (core.default.DefaultArray 8#usize mid.p256.AffineMontPoint.Insts.CoreDefaultDefault) = ok c
  get_or_build_now : ∀ (key : mid.p256.VerifyingKey) (P : Std.Array mid.p256.AffineMontPoint 8#usize → Prop),
    mid.p256.AffineMontPoint.public_odd_multiples key.point ⦃ P ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build_now
      (Array.Insts.CoreMarkerCopy 8#usize mid.p256.AffineMontPoint.Insts.CoreMarkerCopy)
      (core.default.DefaultArray 8#usize mid.p256.AffineMontPoint.Insts.CoreDefaultDefault)
      mid.p256.VerifyingKey.raw_ecdsa_verify.closure.Insts.CoreOpsFunctionFnOnceTupleArrayAffineMontPoint8
      key.odd_multiples key ⦃ P ⦄
  get_or_build : ∀ (key : mid.p256.VerifyingKey) (odd : Std.Array mid.p256.AffineMontPoint 8#usize)
      (P : Std.Array mid.p256.AffineMontPoint 8#usize → Prop),
    mid.p256.AffineMontPoint.public_odd_multiples key.point ⦃ o =>
      mid.p256.AffineMontPoint.public_more_odd_multiples o ⦃ P ⦄ ⦄ →
    mid.p256.AffineMontPoint.public_more_odd_multiples odd ⦃ P ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build
      (Array.Insts.CoreMarkerCopy 8#usize mid.p256.AffineMontPoint.Insts.CoreMarkerCopy)
      (core.default.DefaultArray 8#usize mid.p256.AffineMontPoint.Insts.CoreDefaultDefault)
      mid.p256.VerifyingKey.raw_ecdsa_verify.closure_1.Insts.CoreOpsFunctionFnOnceTupleArrayAffineMontPoint8
      key.more_odd_multiples odd ⦃ r => r = none ∨ ∃ m, r = some m ∧ P m ⦄
  clone : ∀ c, ∃ c', low.generic.reuse_cache.ReuseCache.Insts.CoreCloneClone.clone
      (Array.Insts.CoreMarkerCopy 8#usize mid.p256.AffineMontPoint.Insts.CoreMarkerCopy)
      (core.default.DefaultArray 8#usize mid.p256.AffineMontPoint.Insts.CoreDefaultDefault) c = ok c'
  point_new : ∃ c, low.generic.reuse_cache.ReuseCache.new
      high.ecdsa.EncodedPoint.Insts.CoreMarkerCopy high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault = ok c
  point_get_or_build_now : ∀ (key : P256SigningKey) (P : high.ecdsa.EncodedPoint → Prop),
    high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
      P256C key () ⦃ P ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build_now
      high.ecdsa.EncodedPoint.Insts.CoreMarkerCopy high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault
      (high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint P256C)
      key.public_key key ⦃ P ⦄
  point_get_or_build_now_any : ∀ {T : Type} (build : core.ops.function.FnOnce T Unit high.ecdsa.EncodedPoint)
      (key : P256SigningKey) (t : T), build.call_once t () ⦃ _ => True ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build_now
      high.ecdsa.EncodedPoint.Insts.CoreMarkerCopy high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault
      build key.public_key t ⦃ _ => True ⦄

namespace P256

/-- The ECDSA verification a key's raw check computes, for `r`, `s`, and
`e` the signature's scalars and the hash's. -/
theorem raw_verify_spec (_hr : Runs) (hc : Cached) (key : mid.p256.VerifyingKey)
    (Q : P256Point) (hQ : p256OnCurve Q) (hQo : P256OrderOf Q) (hpt : p256Represents2 Q (pairNat key.point.xy.val))
    (r s e : mid.p256.Scalar) (hr0 : 0 < scNat r) (hr : scNat r < n256) (hs0 : 0 < scNat s)
    (hs : scNat s < n256) (he : scNat e < n256) :
    mid.p256.VerifyingKey.raw_ecdsa_verify key r s e ⦃ res =>
      (ecdsaP256Verifies Q (scNat e) (scNat r) (scNat s) ∧ res = core.result.Result.Ok ()) ∨
        (¬ ecdsaP256Verifies Q (scNat e) (scNat r) (scNat s) ∧
          res = core.result.Result.Err error.Error.BadSignature) ⦄ := by
  unfold mid.p256.VerifyingKey.raw_ecdsa_verify
  have hlt : ∀ x, x % n256 < n256 := fun x => Nat.mod_lt _ n256_pos
  step with scalar_inv_spec s hs0 hs as ⟨si, hsi, hssi⟩
  step with scalar_as_mont_spec si hsi as ⟨sm, hsm⟩
  step with scalar_as_mont_spec e he as ⟨em, hem⟩
  step with scalar_mont_mul_spec sm em (by rw [hsm]; exact hlt _) (by rw [hem]; exact hlt _) as ⟨s3, hs3⟩
  step as ⟨u1, hu1⟩
  step with scalar_as_mont_spec r hr as ⟨rm, hrm⟩
  step with scalar_mont_mul_spec sm rm (by rw [hsm]; exact hlt _) (by rw [hrm]; exact hlt _) as ⟨s5, hs5⟩
  step as ⟨u2, hu2⟩
  have hodd_spec := odd_multiples_spec _hr key.point Q hQ hQo hpt
  step with hc.get_or_build_now key _ hodd_spec as ⟨odd, hodd⟩
  step with hc.get_or_build key odd _ (WP.spec_mono hodd_spec fun o ho => more_odd_spec _hr Q hQ hQo o ho)
    (more_odd_spec _hr Q hQ hQo odd hodd) as ⟨more, hmore⟩
  have hs' : (scNat s : ZMod n256) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hs0 hs
  have hsinv : (scNat si : ZMod n256) = (scNat s : ZMod n256)⁻¹ := by
    have := congrArg (fun x : Nat => (x : ZMod n256)) hssi
    simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at this
    exact (inv_eq_of_mul_eq_one_right this).symm
  have hR := RInv_mul
  push_cast at hR
  have hu1v : scNat u1 = ((scNat e : ZMod n256) * (scNat s : ZMod n256)⁻¹).val := by
    apply val_of_eq _ _ (by rw [hu1]; exact hlt _)
    simp only [scNat] at *
    rw [hu1, hs3, hsm, hem]
    push_cast [ZMod.natCast_mod]
    rw [hsinv]
    set t : ZMod n256 := (2 ^ 256 : ZMod n256) * (n256RInv : ZMod n256)
    linear_combination (scNat s : ZMod n256)⁻¹ * (scNat e : ZMod n256) * (t + 1) * hR
  have hu2v : scNat u2 = ((scNat r : ZMod n256) * (scNat s : ZMod n256)⁻¹).val := by
    apply val_of_eq _ _ (by rw [hu2]; exact hlt _)
    simp only [scNat] at *
    rw [hu2, hs5, hsm, hrm]
    push_cast [ZMod.natCast_mod]
    rw [hsinv]
    set t : ZMod n256 := (2 ^ 256 : ZMod n256) * (n256RInv : ZMod n256)
    linear_combination (scNat s : ZMod n256)⁻¹ * (scNat r : ZMod n256) * (t + 1) * hR
  have hmore' : ∀ m, more = some m → OddMultiples Q 17 m := by
    intro m hm
    rcases hmore with h | ⟨m', h, hm'⟩
    · rw [h] at hm; cases hm
    · rw [h] at hm; cases hm; exact hm'
  step with twin_multiply_spec _hr u1 u2 Q hQ odd hodd more hmore' as ⟨pt, hpt⟩
  rw [twin, show ((scNat u1 : Nat) : Int) = Int.ofNat (scNat u1) from rfl, show ((scNat u2 : Nat) : Int) = Int.ofNat (scNat u2) from rfl] at hpt
  simp only [p256ZPow] at hpt
  rw [hu1v, hu2v] at hpt
  unfold ecdsaP256Verifies nist.ecdsaVerifies
  dsimp only [p256Add, p256Pow] at hpt
  rcases hT : nist.add p256 (nist.pow p256 p256G ((scNat e : ZMod n256) * (scNat s : ZMod n256)⁻¹).val)
      (nist.pow p256 Q ((scNat r : ZMod n256) * (scNat s : ZMod n256)⁻¹).val) with _ | ⟨x, y⟩
  · rw [hT] at hpt
    step with is_infinity_spec pt none hpt as ⟨b, hb⟩
    rw [ite_eq_left (hb.mpr trivial)]
    simp only [WP.spec_ok]
    right
    simp
  · rw [hT] at hpt
    step with is_infinity_spec pt _ hpt as ⟨b, hb⟩
    have hbf : ¬ b = true := fun h => by cases hb.mp h
    rw [ite_eq_right hbf]
    step with x_is_spec _hr pt x y hpt r hr as ⟨b1, hb1⟩
    split
    · rename_i h1
      rw [WP.spec_ok]
      left
      exact ⟨hr0, hr, hs0, hs, hb1.mp h1, rfl⟩
    · rename_i h1
      rw [WP.spec_ok]
      right
      exact ⟨fun h => h1 (hb1.mpr h.2.2.2.2), rfl⟩

/-! ## Verifying keys, `mid::p256::VerifyingKey` -/

/-- An X9.62 key's parse outcome: refused unless an uncompressed point on the
curve, with coordinates below p, and otherwise `good` of what it builds. -/
def x962Outcome {α : Type} (bytes : List U8) (good : α → Prop) (r : core.result.Result α error.Error) :
    Prop :=
  match bytes.head? with
  | none => r = .Err (.KeyRejected .WrongLength)
  | some b0 =>
    if b0 = 4#u8 then
      if bytes.length = 65 then
        if p256OnCurve (some (x962Coords bytes)) then ∃ a, r = .Ok a ∧ good a
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength)
    else r = .Err (.KeyRejected .Compressed)

/-- A verifying key for the point `Q`. -/
def VKey (Q : P256Point) (key : mid.p256.VerifyingKey) : Prop :=
  p256OnCurve Q ∧ Q ≠ none ∧ p256Represents2 Q (pairNat key.point.xy.val)

theorem vk_from_x962_spec (h : Runs) (hheld : Held) (hc : Cached) (bytes : Slice U8) :
    mid.p256.VerifyingKey.from_x962_uncompressed bytes ⦃ r =>
      x962Outcome bytes.val (VKey (some (x962Coords bytes.val))) r ⦄ := by
  unfold mid.p256.VerifyingKey.from_x962_uncompressed
  rw [hheld]
  simp only [bind_ok]
  step with public_from_x962_spec h bytes as ⟨r, hr⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  unfold x962Outcome
  rcases hb : bytes.val.head? with _ | b0
  · simp only [hb] at hr; subst hr; simp
  · simp only [hb] at hr ⊢
    by_cases h4 : b0 = 4#u8 <;> simp only [h4, ↓reduceIte] at hr ⊢
    · by_cases hl : bytes.length = 65 <;> simp only [hl, ↓reduceIte] at hr ⊢
      · by_cases hon : p256OnCurve (some (x962Coords bytes.val)) <;> simp only [hon, ↓reduceIte] at hr ⊢
        · obtain ⟨pk, rfl, hpk⟩ := hr
          simp only
          obtain ⟨c, hcv⟩ := hc.new
          rw [hcv]
          simp only [bind_ok, WP.spec_ok]
          exact ⟨_, rfl, hon, by simp, hpk⟩
        · subst hr; simp
      · subst hr; simp
    · subst hr; simp

/-! ## The generic ECDSA layer, `high::ecdsa`, at P-256 -/

theorem from_bytes_reduced_spec (bytes : Slice U8) (hl : bytes.length = 32) :
    mid.p256.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced bytes ⦃ sc =>
      scNat sc = beNat bytes.val % n256 ⦄ := by
  unfold mid.p256.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced mid.p256.Scalar.from_bytes_reduced
  step with be_any_size_32_spec bytes hl as ⟨o, w, ho, hw⟩
  subst ho
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨r, hr⟩
  simp only [core.result.Result.unwrap, WP.spec_ok]
  simp only [scNat] at *
  rw [hr, hw]

/-- Signature verification's outcome under the key `Q`, for the message's
digest `dg`: accepted if `sig` is 64 bytes, its halves big-endian r and s,
that verify over the digest's first 32 bytes, and otherwise refused. -/
def ecdsaVerifyOutcome (Q : P256Point) (dg sig : List U8) (r : core.result.Result Unit error.Error) : Prop :=
  (sig.length = 64 ∧ ecdsaP256Verifies Q (beNat (dg.take 32) % n256) (beNat (sig.take 32)) (beNat (sig.drop 32)) ∧
    r = .Ok ()) ∨
  (¬ (sig.length = 64 ∧
      ecdsaP256Verifies Q (beNat (dg.take 32) % n256) (beNat (sig.take 32)) (beNat (sig.drop 32))) ∧
    r = .Err .BadSignature)

theorem hash_to_scalar_spec (dg : Slice U8) (hdg : 32 ≤ dg.length) :
    high.ecdsa.hash_to_scalar P256C dg ⦃ r =>
      ∃ e, r = .Ok e ∧ scNat e = beNat (dg.val.take 32) % n256 ⦄ := by
  unfold high.ecdsa.hash_to_scalar
  simp only [mid.p256.Scalar.Insts.RindHighCurveScalar.LEN_BYTES, mid.p256.Scalar.BYTES, 
    bind_ok]
  apply WP.spec_bind (Pₘ := fun h32 : Slice U8 => h32.val = dg.val.take 32)
  · split
    · step as ⟨h32, hh32, _⟩
      simp [hh32, List.slice]
    · rename_i hle
      simp only [WP.spec_ok]
      rw [List.take_of_length_le]
      have : ¬ dg.length > 32 := by simpa [Slice.len] using hle
      simp only [Slice.length] at hdg this ⊢; omega
  intro h32 hh32
  have hl : h32.length = 32 := by
    simp only [Slice.length, hh32, List.length_take]; simp only [Slice.length] at hdg; omega
  step with from_bytes_reduced_spec h32 hl as ⟨e, he⟩
  rw [hh32] at he
  exact ⟨e, rfl, he⟩

theorem ecdsa_verify_spec (h : Runs) (hc : Cached) {H Ctx St : Type}
    (hinst : high.hash.SignatureHash H Ctx St)
    (key : high.ecdsa.VerifyingKey high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey mid.p256.Scalar)
    (Q : P256Point) (hk : VKey Q key.public_key) (hQo : P256OrderOf Q) (msg sig dg : Slice U8)
    (d : high.digest.Digest) (hd : hinst.HashInst.hash msg = ok d)
    (hdg' : high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg) (hdg : 32 ≤ dg.length) :
    high.ecdsa.VerifyingKey.verify P256C hinst key msg sig ⦃ r => ecdsaVerifyOutcome Q dg.val sig.val r ⦄ := by
  unfold high.ecdsa.VerifyingKey.verify
  step
  simp only [mid.p256.Scalar.Insts.RindHighCurveScalar.LEN_BYTES, mid.p256.Scalar.BYTES]
  step as ⟨i2, hi2⟩
  unfold ecdsaVerifyOutcome
  by_cases hlen : sig.length = 64
  · have hne : (sig.len != i2) = false := by
      simp only [bne_eq_false_iff_eq]; apply UScalar.eq_of_val_eq; simp [Slice.len, hi2]
      simpa [Slice.length] using hlen
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hlen, true_and]
    have hsl : sig.val.length = 64 := hlen
    step as ⟨sr, hsr, hsrl⟩
    have hsrv : sr.val = sig.val.take 32 := by rw [hsr]; simp [List.slice]
    unfold mid.p256.Scalar.Insts.RindHighCurveScalar.from_bytes_checked
    step with from_bytes_checked_spec sr hsrl as ⟨rr, hrr⟩
    rw [hsrv] at hrr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      
      high.ecdsa.VerifyingKey.verify.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      
      high.ecdsa.VerifyingKey.verify.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    by_cases hra : 0 < beNat (sig.val.take 32) ∧ beNat (sig.val.take 32) < n256
    · rw [ite_eq_left hra] at hrr
      obtain ⟨scr, rfl, hscr⟩ := hrr
      simp only [bind_ok]
      step as ⟨ss, hss, hssl⟩
      have hssv : ss.val = sig.val.drop 32 := by simp [hss]
      step with from_bytes_checked_spec ss (by rw [hssl]; simp only [Slice.length]; omega) as ⟨rs, hrs⟩
      rw [hssv] at hrs
      by_cases hsa : 0 < beNat (sig.val.drop 32) ∧ beNat (sig.val.drop 32) < n256
      · rw [ite_eq_left hsa] at hrs
        obtain ⟨scs, rfl, hscs⟩ := hrs
        simp only [bind_ok]
        rw [hd]
        simp only [bind_ok]
        rw [hdg']
        simp only [bind_ok]
        step with hash_to_scalar_spec dg hdg as ⟨r4, e, hr4, he⟩
        subst hr4
        simp only [bind_ok, mid.p256.VerifyingKey.Insts.RindHighCurvePublicKeyScalar.raw_ecdsa_verify]
        obtain ⟨hQ, -, hpt⟩ := hk
        apply WP.spec_mono (raw_verify_spec h hc key.public_key Q hQ hQo hpt scr scs e
          (by unfold scNat; rw [hscr]; exact hra.1) (by unfold scNat; rw [hscr]; exact hra.2)
          (by unfold scNat; rw [hscs]; exact hsa.1) (by unfold scNat; rw [hscs]; exact hsa.2)
          (by rw [he]; exact Nat.mod_lt _ n256_pos))
        intro r hr
        simp only [scNat] at hr he
        rw [hscr, hscs, he] at hr
        rcases hr with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
        · left; exact ⟨hv, rfl⟩
        · right; exact ⟨hv, rfl⟩
      · rw [ite_eq_right hsa] at hrs
        subst hrs
        simp only [bind_ok, WP.spec_ok]
        right
        exact ⟨fun hv => hsa ⟨hv.2.2.1, hv.2.2.2.1⟩, trivial⟩
    · rw [ite_eq_right hra] at hrr
      subst hrr
      simp only [bind_tc_ok, bind_ok, WP.spec_ok]
      right
      exact ⟨fun hv => hra ⟨hv.1, hv.2.1⟩, rfl⟩
  · have hne : (sig.len != i2) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hlen
      have := congrArg UScalar.val he; simp [Slice.len, hi2] at this; simpa [Slice.length] using this
    simp only [hne, ↓reduceIte, WP.spec_ok, hlen, false_and, not_false_eq_true, true_and, or_true]

/-- `ecdsa::VerifyingKey::from_x962_uncompressed` at P-256. -/
theorem ecdsa_vk_from_x962_spec (h : Runs) (hheld : Held) (hc : Cached) (bytes : Slice U8) :
    high.ecdsa.VerifyingKey.from_x962_uncompressed P256C bytes ⦃ r =>
      x962Outcome bytes.val (fun key => VKey (some (x962Coords bytes.val)) key.public_key) r ⦄ := by
  unfold high.ecdsa.VerifyingKey.from_x962_uncompressed
  step
  simp only [P256C, 
    mid.p256.VerifyingKey.Insts.RindHighCurvePublicKeyScalar,
    mid.p256.VerifyingKey.Insts.RindHighCurvePublicKeyScalar.from_x962_uncompressed]
  step with vk_from_x962_spec h hheld hc bytes as ⟨r, hr⟩
  simp only [core.result.Result.map,
    
    high.ecdsa.VerifyingKey.from_x962_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleClause0_PublicKeyVerifyingKey.call_once]
  unfold x962Outcome at hr ⊢
  rcases hb : bytes.val.head? with _ | b0
  · simp only [hb] at hr; subst hr; simp
  · simp only [hb] at hr ⊢
    split_ifs at hr ⊢
    · obtain ⟨k, rfl, hk⟩ := hr; simp [hk]
    all_goals (subst hr; simp)

/-! ## Signing's r, `StaticPrivateKey::public_key_x_scalar` -/

theorem x_scalar_spec (k : mid.p256.StaticPrivateKey) (h : Runs) (hk : scNat k.scalar < n256) (x y : Nat)
    (hq : p256Pow p256G (scNat k.scalar) = some (x, y)) (hc : p256OnCurve (some (x, y))) :
    mid.p256.StaticPrivateKey.public_key_x_scalar k ⦃ r => scNat r = x % n256 ⦄ := by
  unfold mid.p256.StaticPrivateKey.public_key_x_scalar mid.p256.AffineMontPoint.x_scalar
  step
  step with public_point_spec h k hk x y hq hc as ⟨pt, hpt⟩
  have hp : 0 < p256 := p256_pos
  step with as_bytes_uncompressed_spec h pt (by rw [hpt]; exact Nat.mod_lt _ hp)
    (by rw [hpt]; exact Nat.mod_lt _ hp) as ⟨b, hb4, hbc⟩
  rw [hpt] at hbc
  simp only [rinv_tomont _ hc.1, rinv_tomont _ hc.2.1] at hbc
  simp only [mid.p256.Scalar.BYTES]
  step as ⟨i, hi⟩
  step as ⟨sl, hsl, hsll⟩
  have hbl : b.val.length = 65 := b.property
  have hslv : beNat sl.val = x := by
    have := congrArg Prod.fst hbc
    simp only [x962Coords] at this
    rw [← this, hsl, Array.val_to_slice]
    simp [hi]
  show mid.p256.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced sl ⦃ _ ⦄
  apply WP.spec_mono (from_bytes_reduced_spec sl (by rw [hsll]; simp [hi]))
  intro r hr
  rw [hr, hslv]

@[step]
theorem is_zero_spec (a : mid.p256.Scalar) :
    mid.p256.Scalar.is_zero a ⦃ b => b ↔ scNat a = 0 ⦄ := by
  unfold mid.p256.Scalar.is_zero mid.p256.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step as ⟨b, hb⟩
  have : wordsNat (Array.repeat 4#usize core.default.DefaultU64.default).val = 0 := by
    simp [wordsNat, Array.repeat, Nat.ofDigits, core.default.DefaultU64.default]
  rw [hb, this]
  simp [scNat]

end P256

/-- A random source whose draws return without panicking, and fail only with
`RngFailed`. -/
def Draws {T : Type} (inst : mid.rng.RandomSource T) : Prop :=
  ∀ rng s, inst.fill rng s ⦃ r => ∀ e, r.1 = .Err e → e = .RngFailed ⦄

namespace P256

/-- A generated key is in [1, n), and generation refuses only with `RngFailed`. -/
def Keygen (res : core.result.Result mid.p256.PrivateKey error.Error) : Prop :=
  (∀ k, res = .Ok k → 0 < wordsNat k.scalar.val ∧ wordsNat k.scalar.val < n256) ∧
    ∀ e, res = .Err e → e = .RngFailed

theorem generate_from_loop_spec {T : Type} (inst : mid.rng.RandomSource T) (hd : Draws inst) (n : Nat)
    (rng : T) : mid.p256.PrivateKey.generate_from_loop inst n rng ⦃ res => Keygen res.1 ⦄ := by
  induction n generalizing rng with
  | zero => simp [mid.p256.PrivateKey.generate_from_loop, Keygen]
  | succ n ih =>
    simp only [mid.p256.PrivateKey.generate_from_loop, Array.to_slice_mut, lift, bind_ok]
    apply WP.spec_bind (hd rng _)
    rintro ⟨r1, rng1, s1⟩ hr1
    rcases r1 with _ | e
    · have hl : ((Array.repeat 32#usize 0#u8).from_slice s1).to_slice.length = 32 := by simp [Slice.length]
      step with from_bytes_spec _ hl as ⟨p, hp⟩
      split_ifs at hp with hin
      · obtain ⟨k, rfl, hk⟩ := hp
        show (ok (core.result.Result.Ok k, rng1) : Result _) ⦃ res => Keygen res.1 ⦄
        simp only [WP.spec_ok, Keygen]
        refine ⟨fun k' hk' => ?_, fun e h => nomatch h⟩
        cases hk'
        rw [hk]; exact hin
      · subst hp
        exact ih rng1
    · show (ok (core.result.Result.Err e, rng1) : Result _) ⦃ res => Keygen res.1 ⦄
      simp only [WP.spec_ok, Keygen]
      exact ⟨fun k h => (nomatch h), fun e' h => by cases h; exact hr1 e rfl⟩

/-- `p256::StaticPrivateKey::generate`, P-256's `generate_random_key`. -/
theorem static_generate_spec (h : Runs) {T : Type} (inst : mid.rng.RandomSource T) (hd : Draws inst)
    (rng : T) : mid.p256.StaticPrivateKey.generate inst rng ⦃ res => Keygen res.1 ⦄ := by
  unfold mid.p256.StaticPrivateKey.generate
  step
  step
  exact generate_from_loop_spec inst hd 64 rng

/-- The nonce loop: if it returns a signature, it is (r, s) for some nonce in
[1, n), with neither zero. -/
theorem sign_nonces_spec (h : Runs) {T : Type}
    (inst : mid.rng.RandomSource T) (hdr : Draws inst)
    (key : high.ecdsa.SigningKey high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey mid.p256.Scalar)
    (hd : scNat key.private_key.scalar < n256)
    (e : mid.p256.Scalar) (he : scNat e < n256) (rng : T) :
    high.ecdsa.SigningKey.sign_with_nonces_loop P256C inst key e rng ⦃ res =>
      (∀ rs, res.1 = .Ok rs → ∃ k, 0 < k ∧ k < n256 ∧
        ecdsaP256Sign (scNat key.private_key.scalar) k (scNat e) = some (scNat rs.1, scNat rs.2) ∧
        scNat rs.1 ≠ 0 ∧ scNat rs.2 ≠ 0) ∧ ∀ err, res.1 = .Err err → err = .RngFailed ⦄div := by
  unfold high.ecdsa.SigningKey.sign_with_nonces_loop
  revert rng
  dspec_induction loop
  intros loop' ih x
  simp only
  unfold high.ecdsa.SigningKey.sign_with_nonces_loop.body
  simp only [
    
    mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.public_key_x_scalar,
    mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.raw_ecdsa_sign,
    mid.p256.Scalar.Insts.RindHighCurveScalar.is_zero,
    ]
  step with static_generate_spec h inst hdr x as ⟨res, hres⟩
  obtain ⟨hok, herr⟩ := hres
  obtain ⟨rr, nx⟩ := res
  simp only at hok herr ⊢
  rcases rr with k | err
  · obtain ⟨hk0, hk⟩ := hok k rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨x, y, hq, hc⟩ := g_mult _ hk0 hk
    step with x_scalar_spec k h hk x y hq hc as ⟨r1, hr1⟩
    step as ⟨b, hb⟩
    split
    · rename_i hbt
      simp only [bind_ok]
      exact ih nx
    · rename_i hbf
      have hr0 : scNat r1 ≠ 0 := fun h0 => hbf (hb.mpr h0)
      step with raw_ecdsa_sign_spec key.private_key k e r1 hd hk0 hk he (by rw [hr1]; exact Nat.mod_lt _ n256_pos)
        as ⟨s1, hs1⟩
      step as ⟨b1, hb1⟩
      split
      · simp only [bind_ok]
        exact ih nx
      · rename_i hb1f
        have hs0 : scNat s1 ≠ 0 := fun h0 => hb1f (hb1.mpr h0)
        simp only [bind_ok, WP.dspec_ok]
        refine ⟨fun rs hrs => ?_, fun err h => by cases h⟩
        cases hrs
        refine ⟨scNat k.scalar, hk0, hk, ?_, hr0, hs0⟩
        simp only [ecdsaP256Sign, nist.ecdsaSign, hq, hr1, hs1]
  · simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.dspec_ok]
    refine ⟨(fun rs h => nomatch h), fun e2 h => ?_⟩
    simp only [core.convert.FromSame.from, core.result.Result.Err.injEq] at h
    rw [← h]; exact herr err rfl

@[step]
theorem write_bytes_spec (sc : mid.p256.Scalar) (target : Slice U8) (hl : target.length = 32) :
    mid.p256.Scalar.Insts.RindHighCurveScalar.write_bytes sc target ⦃ r =>
      r.length = 32 ∧ beNat r.val = scNat sc ⦄ := by
  unfold mid.p256.Scalar.Insts.RindHighCurveScalar.write_bytes mid.p256.Scalar.as_bytes
  step as ⟨a, ha⟩
  step as ⟨sl, hsl⟩
  step as ⟨r, hr⟩
  refine ⟨by simp [Slice.length, hr, hsl], ?_⟩
  rw [hr, hsl, Array.val_to_slice, ha]

theorem encode_spec (k : mid.p256.StaticPrivateKey) (out : Slice U8) (hl : 32 ≤ out.length) :
    mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.encode k out ⦃ r =>
      ∃ sl, r.1 = .Ok sl ⦄ := by
  unfold mid.p256.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.encode
  simp only [core.slice.Slice.get_mut, 
    core.slice.index.SliceIndexRangeUsizeSlice.get_mut]
  rw [ite_eq_left (by simp; omega)]
  simp only [bind_ok, mid.p256.StaticPrivateKey.secret_bytes, mid.p256.PrivateKey.secret_bytes,
    mid.p256.Scalar.as_bytes]
  step*

end P256

/-- The HMAC-DRBG an ECDSA signature draws its nonces from, which the
translation leaves opaque, since its update takes a slice of borrowed slices:
it is seeded, and draws, without panicking, and a draw never fails. A draw
asserts that its reseed counter, one more than the draws it has made, is below
2⁴⁸. -/
structure Drbg : Prop where
  seeds : ∀ {H C S : Type} (inst : high.hash.Hash H C S) (a b c : Slice U8),
    ∃ g, high.hmac_drbg.HmacDrbg.new inst a b c = ok g
  draws : ∀ {H C S : Type} (inst : high.hash.Hash H C S) g (s : Slice U8),
    ∃ g' s', high.hmac_drbg.HmacDrbg.Insts.RindMidRngRandomSource.fill inst g s = ok (.Ok (), g', s')

theorem Drbg.draws_spec (hdrbg : Drbg) {H C S : Type} (inst : high.hash.Hash H C S) :
    Draws (high.hmac_drbg.HmacDrbg.Insts.RindMidRngRandomSource inst) := by
  intro g s
  obtain ⟨g', s', hf⟩ := hdrbg.draws inst g s
  simp [hf]

namespace P256

/-- An ECDSA signature's outcome, for private key `d` and the hash's integer
`e`: 64 bytes at the start of the output, the big-endian r and s of some
nonce in [1, n), neither zero; refused if the output is short or the nonce
source fails. -/
def ecdsaSignOutcome (d e : Nat) (outLen : Nat)
    (r : core.result.Result (Slice U8) error.Error × Slice U8) : Prop :=
  (∀ out, r.1 = .Ok out → out.length = 64 ∧ r.2.length = outLen ∧ r.2.val.take 64 = out.val ∧
    ∃ k, 0 < k ∧ k < n256 ∧
    ecdsaP256Sign d k e = some (beNat (out.val.take 32), beNat (out.val.drop 32)) ∧
    beNat (out.val.take 32) ≠ 0 ∧ beNat (out.val.drop 32) ≠ 0) ∧
  ∀ err, r.1 = .Err err → (outLen < 64 ∧ err = .WrongLength) ∨ err = .RngFailed

theorem p256c_len : P256C.ScalarInst.LEN_BYTES = ok 32#usize := by
  simp only [
    mid.p256.Scalar.Insts.RindHighCurveScalar.LEN_BYTES,
    mid.p256.Scalar.BYTES]

theorem get_mut_rangeTo (s : Slice U8) (r : core.ops.range.RangeTo Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexRangeToUsizeSlice U8) s r =
      core.slice.index.SliceIndexRangeToUsizeSlice.get_mut r s := rfl

theorem rfc6979_spec (h : Runs) (hdrbg : Drbg) {H Ctx St : Type}
    (hinst : high.hash.Hash H Ctx St)
    (key : high.ecdsa.SigningKey high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey mid.p256.Scalar)
    (hd : scNat key.private_key.scalar < n256)
    (msg random sig dg : Slice U8) (d : high.digest.Digest) (hhash : hinst.hash msg = ok d)
    (hdg' : high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg) (hdg : 32 ≤ dg.length) :
    high.ecdsa.SigningKey.rfc6979_sign_with_random P256C hinst key msg random sig ⦃ r =>
      ecdsaSignOutcome (scNat key.private_key.scalar) (beNat (dg.val.take 32) % n256) sig.length r ⦄div := by
  unfold high.ecdsa.SigningKey.rfc6979_sign_with_random
  rw [p256c_len]
  simp only [bind_ok]
  step as ⟨i1, hi1⟩
  rw [get_mut_rangeTo]
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  have hsl' : sig.val.length = sig.length := rfl
  by_cases hlen : 64 ≤ sig.length
  swap
  · rw [ite_eq_right (by rw [hi1]; simp; omega)]
    simp only [uncurry, bind_ok, WP.dspec_ok, ecdsaSignOutcome]
    refine ⟨(fun out h => nomatch h), fun err h => ?_⟩
    cases h; left; exact ⟨by omega, rfl⟩
  rw [ite_eq_left (by rw [hi1]; simp; omega)]
  simp only [uncurry, bind_ok]
  rw [hhash]
  simp only [bind_ok]
  step as ⟨s, back, hs, hback⟩
  step with encode_spec key.private_key s (by simp [Slice.length, hs, Array.repeat]) as ⟨er, eb, sl, hsl⟩
  rw [hsl]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdg']
  simp only [bind_ok]
  step with hash_to_scalar_spec dg hdg as ⟨r1, e, hr1, he⟩
  subst hr1
  simp only [bind_ok]
  step as ⟨s2, back2, hs2, hs2l, hback2⟩
  step with write_bytes_spec e s2 (by simp [Slice.length, hs2, Array.repeat, List.slice]) as ⟨s3, hs3l, hs3⟩
  step as ⟨s4, hs4, hs4l⟩
  obtain ⟨g, hg⟩ := hdrbg.seeds hinst sl s4 random
  rw [hg]
  simp only [bind_ok, high.ecdsa.SigningKey.sign_with_nonces]
  apply WP.dspec_bind (sign_nonces_spec h _ (hdrbg.draws_spec hinst) key hd e (by rw [he]; exact Nat.mod_lt _ n256_pos) g)
  rintro ⟨r2, g2⟩ ⟨hr2ok, hr2err⟩
  simp only at hr2ok hr2err
  simp only [uncurry]
  rcases r2 with ⟨rr, ss⟩ | err
  · obtain ⟨k, hk0, hk, hsign, hr0, hs0⟩ := hr2ok _ rfl
    simp only [bind_ok]
    step as ⟨s6, back6, hs6, hs6l, hback6⟩
    step with write_bytes_spec rr s6 (by rw [hs6l]) as ⟨s7, hs7l, hs7⟩
    set O := List.slice 0 i1.val sig.val with hOdef
    have hOl : O.length = 64 := by simp [hOdef, List.slice, hi1]; omega
    have h6 : (back6 s7).val = s7.val ++ O.drop 32 := by
      rw [hback6, Slice.from_val]
      have := setSlice!_append [] (O.take 32) (O.drop 32) s7.val (by simp [Slice.length] at hs7l; simp [hs7l, hOl])
      simp only [List.nil_append, List.take_append_drop, List.length_nil] at this
      rw [← this]
    have hs7l' : s7.val.length = 32 := hs7l
    have hb6l : (back6 s7).val.length = 64 := by simp [h6, hs7l', hOl]
    step as ⟨s8, back8, hs8, hs8l, hback8⟩
    have hs8v : s8.length = 32 := by rw [hs8l]; simp only [Slice.length, hb6l]
    step with write_bytes_spec ss s8 hs8v as ⟨s9, hs9l, hs9⟩
    have h8 : (back8 s9).val = s7.val ++ s9.val := by
      rw [hback8, h6]
      have := setSlice!_append s7.val (O.drop 32) [] s9.val (by simp [Slice.length] at hs9l; simp [hs9l, hOl])
      simp only [List.append_nil, hs7l'] at this
      exact this
    step as ⟨i2, hi2⟩
    step as ⟨s10, hs10, hs10l⟩
    simp only [WP.dspec_ok, ecdsaSignOutcome]
    have hs9l' : s9.val.length = 32 := hs9l
    have hv : s10.val = s7.val ++ s9.val := by
      rw [hs10, h8, hi2]; simp [List.slice, hs7l', hs9l']
    refine ⟨fun out hout => ?_, fun err h => nomatch h⟩
    cases hout
    have hb8 : (back8 s9).val.length = 64 := by simp [h8, hs7l', hs9l']
    have hb8l : (back8 s9).length = i1.val := by simp only [Slice.length, hb8, hi1]
    refine ⟨by simp [Slice.length, hv, hs7l', hs9l'], ?_, ?_, k, hk0, hk, ?_⟩
    · simp only [hb8l, ↓reduceDIte]
      simp [Slice.length]
    · simp only [hb8l, ↓reduceDIte, Slice.from_val]
      have := take_setSlice! sig.val (back8 s9).val 0 (by omega)
      simp only [zero_add, hb8, List.take_zero, List.nil_append] at this
      rw [this, hv, h8]
    rw [hv, List.take_left' hs7l', List.drop_left' hs7l', hs7, hs9, ← he]
    exact ⟨hsign, hr0, hs0⟩
  · simp only [bind_tc_ok, bind_ok, 
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.dspec_ok, ecdsaSignOutcome]
    refine ⟨(fun out h => nomatch h), fun e2 h => ?_⟩
    cases h; right; exact hr2err _ rfl

end P256

/-- The system random source, `getrandom::fill`, returns without panicking;
what it draws the functional spec leaves out. -/
def Fills : Prop := ∀ s : Slice U8, ∃ r, getrandom.fill s = ok r

namespace P256

/-- `ecdsa::SigningKey::sign` at P-256. -/
theorem ecdsa_sign_spec (h : Runs) (hdrbg : Drbg) (hfill : Fills)
    {H Ctx St : Type} (hinst : high.hash.SignatureHash H Ctx St)
    (key : high.ecdsa.SigningKey high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey mid.p256.Scalar)
    (hd : scNat key.private_key.scalar < n256)
    (msg sig dg : Slice U8) (d : high.digest.Digest) (hhash : hinst.HashInst.hash msg = ok d)
    (hdg' : high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg) (hdg : 32 ≤ dg.length) :
    high.ecdsa.SigningKey.sign P256C hinst key msg sig ⦃ r =>
      ecdsaSignOutcome (scNat key.private_key.scalar) (beNat (dg.val.take 32) % n256) sig.length r ⦄div := by
  unfold high.ecdsa.SigningKey.sign mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill
  step
  step as ⟨rs, back, hrs, hback⟩
  obtain ⟨⟨fr, fs⟩, hf⟩ := hfill rs
  rw [hf]
  simp only [bind_ok, uncurry]
  rcases fr with _ | ferr
  · simp only [core.result.Result.map_err, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨rnd, hrnd⟩
    exact rfc6979_spec h hdrbg hinst.HashInst key hd msg rnd sig dg d hhash hdg' hdg
  · simp only [core.result.Result.map_err, bind_tc_ok, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      
      mid.rng.RandomSourceSystemRandom.fill.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ecdsaSignOutcome]
    simp

end P256

end rind.x86_64
