import Rind.X86_64.P384Keygen
import Rind.X86_64.P256Ecdsa
import Rind.P384Multiples
open Aeneas Aeneas.Std Result rind.spec
open rind.x86_64.Naf (nafVal nafDigit nafVal_drop naf_spec)

/-!
# P-384 ECDSA, proven from rind's signature API to s2n-bignum's contracts

The proof follows `Rind.X86_64.P256Ecdsa`'s, over P-384's field and point
lemmas in `Rind.X86_64.P384` and `Rind.X86_64.P384Keygen`. The twin
multiplication of verification looks the generator's multiples up in the
first comb table, which `Rind.X86_64.P384Table` checks holds G to 16G; key
generation and each signature's k·G run pyca/verified-garbage's `d·G` where
`MulBase::check` passes, and otherwise the comb `Rind.X86_64.P384Keygen`
proves; verification runs VG's routine where `Verify::check` passes, on
aarch64 only until a key's multiples are ready, and otherwise rind's own.
`Rind.X86_64.VgP384` states VG's routines' contracts. `admin/prove` writes
the aarch64 proof from this file by renaming the target.
-/

set_option exponentiation.threshold 400

namespace rind.x86_64

namespace P384

/-! ## Scalars mod n, `mid::p384::Scalar` -/

/-- HOL Light's `inverse_mod n_384 (2 EXP 384)`. -/
def n384RInv : Nat :=
  8213155180316830564023772752902517460134849974600554980379995049303147060140144611822562736815346652390458105321745

theorem n384RInv_spec : 2 ^ 384 * n384RInv % n384 = 1 % n384 := by
  simp only [n384RInv, n384]; decide

theorem n384_lt : n384 < 2 ^ 384 := by unfold n384; decide

theorem n384_odd : n384 % 2 = 1 := by unfold n384; decide

theorem CURVE_ORDER_val : wordsNat mid.p384.CURVE_ORDER.val = n384 := by
  simp only [mid.p384.CURVE_ORDER, Array.make, wordsNat, n384]; decide

/-- `CURVE_ORDER_MM`, 2⁷⁶⁸ mod n, the Montgomery form of 2³⁸⁴. -/
def n384MM : Nat :=
  1926889955270807207284364373743377144127886613064468223890781010531391223293594548775097723903321707631980877973929

theorem n384MM_spec : n384MM < n384 ∧ n384RInv * n384MM % n384 = 2 ^ 384 % n384 := by
  unfold n384MM n384RInv n384; decide

theorem CURVE_ORDER_MM_val : wordsNat mid.p384.CURVE_ORDER_MM.val = n384MM := by
  simp only [mid.p384.CURVE_ORDER_MM, Array.make, wordsNat, n384MM]; decide

/-- The number a scalar's limbs encode. -/
abbrev scNat (s : mid.p384.Scalar) : Nat := wordsNat s.val

theorem repeat_length6 : (Array.repeat 6#usize core.default.DefaultU64.default).val.length = 6 := by
  simp [Array.repeat]

/-- A result written through a scalar's slice is the scalar with its limbs. -/
theorem from_slice6 (s s4 : Slice U64) (hs : s.val = (Array.repeat 6#usize core.default.DefaultU64.default).val)
    (h : s4.length = s.length) :
    ((Array.repeat 6#usize core.default.DefaultU64.default).from_slice s4).val = s4.val := by
  apply Array.from_slice_val
  rw [show s4.val.length = s4.length from rfl, h, Slice.length, hs, repeat_length6]; rfl

theorem slice_length6 (s : Slice U64) (hs : s.val = (Array.repeat 6#usize core.default.DefaultU64.default).val) :
    s.length = 6 := by
  rw [Slice.length, hs, repeat_length6]

theorem mul_lt_mont (a b : Nat) (ha : a < n384) (hb : b < n384) : a * b ≤ 2 ^ 384 * n384 :=
  le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (Nat.mul_le_mul_right _ (le_of_lt n384_lt)))

@[step]
theorem scalar_mont_mul_spec (a b : mid.p384.Scalar) (ha : scNat a < n384) (hb : scNat b < n384) :
    mid.p384.Scalar.mont_mul a b ⦃ r => scNat r = n384RInv * scNat a * scNat b % n384 ⦄ := by
  unfold mid.p384.Scalar.mont_mul mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice6 s s4 s_post s4_post]
  rw [slice_length6 s s_post, s1_post, s2_post, s3_post] at s4_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val] at s4_post1
  exact s4_post1 n384_odd (mul_lt_mont _ _ ha hb) n384RInv n384RInv_spec

@[step]
theorem scalar_as_mont_spec (a : mid.p384.Scalar) (ha : scNat a < n384) :
    mid.p384.Scalar.as_mont a ⦃ r => scNat r = 2 ^ 384 * scNat a % n384 ⦄ := by
  unfold mid.p384.Scalar.as_mont mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice6 s s4 s_post s4_post]
  rw [slice_length6 s s_post, s1_post, s2_post, s3_post] at s4_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val, CURVE_ORDER_MM_val] at s4_post1
  rw [s4_post1 n384_odd (mul_lt_mont _ _ ha n384MM_spec.1) n384RInv n384RInv_spec,
    show n384RInv * wordsNat a.val * n384MM = wordsNat a.val * (n384RInv * n384MM) by ring,
    Nat.mul_mod, n384MM_spec.2, ← Nat.mul_mod, Nat.mul_comm (wordsNat a.val)]

@[step]
theorem scalar_demont_spec (a : mid.p384.Scalar) :
    mid.p384.Scalar.demont a ⦃ r => scNat r = n384RInv * scNat a % n384 ⦄ := by
  unfold mid.p384.Scalar.demont mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice6 s s3 s_post s3_post]
  rw [slice_length6 s s_post, s1_post, s2_post] at s3_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val] at s3_post1
  exact s3_post1 n384_odd n384RInv n384RInv_spec

@[step]
theorem scalar_add_spec (a b : mid.p384.Scalar) (ha : scNat a < n384) (hb : scNat b < n384) :
    mid.p384.Scalar.add a b ⦃ r => scNat r = (scNat a + scNat b) % n384 ⦄ := by
  unfold mid.p384.Scalar.add mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  · simpa [s1_post, s3_post, CURVE_ORDER_val] using ha
  · simpa [s2_post, s3_post, CURVE_ORDER_val] using hb
  · rw [to_slice_mut_back_post, scNat, from_slice6 s s4 s_post s4_post]
    simpa [s1_post, s2_post, s3_post, CURVE_ORDER_val] using s4_post1

@[step]
theorem scalar_inv_spec (a : mid.p384.Scalar) (ha0 : 0 < scNat a) (ha : scNat a < n384) :
    mid.p384.Scalar.inv a ⦃ r => scNat r < n384 ∧ scNat a * scNat r % n384 = 1 ⦄ := by
  unfold mid.p384.Scalar.inv mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  rw [to_slice_mut_back_post, scNat, from_slice6 s s4 s_post s4_post]
  rw [s1_post, s2_post] at s4_post1
  simp only [Array.val_to_slice, CURVE_ORDER_val] at s4_post1
  exact s4_post1 ((n384_prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha0 ha)).symm)
    n384_odd (by unfold n384; decide)

theorem n384_pos : 0 < n384 := n384_prime.pos

/-- A number below n is the value of its residue. -/
theorem val_of_eq (x : Nat) (z : ZMod n384) (hx : x < n384) (h : (x : ZMod n384) = z) : x = z.val := by
  rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

theorem RInv_mul : ((2 ^ 384 : Nat) : ZMod n384) * (n384RInv : ZMod n384) = 1 := by
  have := congrArg (fun x : Nat => (x : ZMod n384)) n384RInv_spec
  simpa [Nat.cast_mul] using this

/-- `raw_ecdsa_sign`: (e + rd)/k mod n. -/
theorem raw_ecdsa_sign_spec (d k : mid.p384.StaticPrivateKey) (e r : mid.p384.Scalar)
    (hd : scNat d.scalar < n384) (hk0 : 0 < scNat k.scalar) (hk : scNat k.scalar < n384)
    (he : scNat e < n384) (hr : scNat r < n384) :
    mid.p384.StaticPrivateKey.raw_ecdsa_sign d k e r ⦃ s =>
      scNat s = (((scNat e + scNat r * scNat d.scalar : Nat) : ZMod n384) *
        (scNat k.scalar : ZMod n384)⁻¹).val ⦄ := by
  unfold mid.p384.StaticPrivateKey.raw_ecdsa_sign low.ct.into_public
  have hlt : ∀ x, x % n384 < n384 := fun x => Nat.mod_lt _ n384_pos
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step with scalar_mont_mul_spec a b (by rw [ha]; exact hlt _) (by rw [hb]; exact hlt _) as ⟨c, hc⟩
  step as ⟨c1, hc1⟩
  step with scalar_add_spec c1 e (by rw [hc1]; exact hlt _) he as ⟨c2, hc2⟩
  step with scalar_as_mont_spec c2 (by rw [hc2]; exact hlt _) as ⟨l, hl⟩
  step with scalar_inv_spec k.scalar hk0 hk as ⟨ki, hki, hkk⟩
  step with scalar_mont_mul_spec ki l hki (by rw [hl]; exact hlt _) as ⟨s6, hs6⟩
  apply val_of_eq _ _ (by rw [hs6]; exact hlt _)
  have hkk' : (scNat k.scalar : ZMod n384) * (scNat ki : ZMod n384) = 1 := by
    have := congrArg (fun x : Nat => (x : ZMod n384)) hkk
    simpa [Nat.cast_mul] using this
  have hkinv : (scNat ki : ZMod n384) = (scNat k.scalar : ZMod n384)⁻¹ := by
    exact (inv_eq_of_mul_eq_one_right hkk').symm
  simp only [scNat] at *
  rw [hs6, hl, hc2, hc1, hc, ha, hb]
  push_cast [ZMod.natCast_mod]
  rw [hkinv]
  have hR := RInv_mul
  push_cast at hR
  set t : ZMod n384 := (2 ^ 384 : ZMod n384) * (n384RInv : ZMod n384)
  linear_combination (scNat k.scalar : ZMod n384)⁻¹ *
    ((t ^ 2 + t + 1) * (scNat d.scalar : ZMod n384) * (scNat r : ZMod n384) + (scNat e : ZMod n384)) * hR

/-! ## Field elements, `mid::p384::FieldElement` -/

@[step]
theorem array_eq_spec (a b : Std.Array U64 6#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a b ⦃ r => r ↔ a.val = b.val ⦄ := by
  have : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a b =
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64 a.to_slice b.to_slice := by
    simp [core.array.equality.PartialEqArray.eq, core.slice.cmp.PartialEqSlice.eq, Array.val_to_slice]
  rw [this]
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ (fun x y => by simp [liftFun2]))
  intro r hr
  rw [hr, Slice.eq_iff, Array.val_to_slice, Array.val_to_slice]

@[step]
theorem fe_public_eq_spec (a b : mid.p384.FieldElement) :
    mid.p384.FieldElement.public_eq a b ⦃ r => r ↔ feNat a = feNat b ⦄ := by
  unfold mid.p384.FieldElement.public_eq
  apply WP.spec_mono (array_eq_spec a b)
  intro r hr
  rw [hr]
  exact ⟨fun h => by simp [feNat, h], fun h => wordsNat_inj _ _ (by rw [a.property, b.property]) h⟩

/-- A number's value as a field element in Montgomery form: it times 2⁻³⁸⁴. -/
abbrev dec (x : Nat) : ZMod p384 := (p384RInv : ZMod p384) * x

theorem RInv_ne_zero : (p384RInv : ZMod p384) ≠ 0 := fun h => by
  have := rinv_cast; rw [h, mul_zero] at this; exact zero_ne_one this

theorem cast_mod_p (x : Nat) : ((x % p384 : Nat) : ZMod p384) = x := ZMod.natCast_mod _ _

/-- Numbers below p are equal when their values are. -/
theorem eq_of_dec (x y : Nat) (hx : x < p384) (hy : y < p384) : x = y ↔ dec x = dec y := by
  constructor
  · intro h; rw [h]
  · intro h
    have h' : (x : ZMod p384) = y := mul_left_cancel₀ RInv_ne_zero h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
    exact h'

theorem dec_mont_mul (a b : Nat) : dec (p384RInv * a * b % p384) = dec a * dec b := by
  simp only [dec, cast_mod_p, Nat.cast_mul]; ring

theorem dec_mont_sqr (a : Nat) : dec (p384RInv * a ^ 2 % p384) = dec a ^ 2 := by
  simp only [dec, cast_mod_p, Nat.cast_mul, Nat.cast_pow]; ring

theorem val_dec (x : Nat) : p384RInv * x % p384 = (dec x).val := by
  rw [dec, ← Nat.cast_mul, ZMod.val_natCast]

theorem ofJacobian_dec (x y z : Nat) :
    nist.ofJacobian p384 (p384RInv * x % p384) (p384RInv * y % p384) (p384RInv * z % p384) =
      if dec z = 0 then none
      else some ((dec x * (dec z ^ 2)⁻¹).val, (dec y * (dec z ^ 3)⁻¹).val) := by
  unfold nist.ofJacobian
  simp only [val_dec, ZMod.natCast_val, ZMod.cast_id', id, ZMod.val_eq_zero]

@[step]
theorem is_infinity_spec (pt : mid.p384.JacobianMontPoint) (P : nist.Point) (h : jrep P pt) :
    mid.p384.JacobianMontPoint.public_is_infinity pt ⦃ b => b ↔ P = none ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_is_infinity mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step as ⟨fz, hfz⟩
  step as ⟨b, hb⟩
  obtain ⟨-, -, hzp, hP⟩ := h
  rw [ofJacobian_dec] at hP
  rw [← hfz] at hzp hP
  have h0 : feNat (Array.repeat 6#usize core.default.DefaultU64.default) = 0 := by
    simp [feNat, wordsNat, Array.repeat, Nat.ofDigits, core.default.DefaultU64.default]
  rw [hb, h0, ← hP]
  constructor
  · intro hz0; rw [hz0]; simp
  · intro hn
    by_contra hz0
    have : dec (feNat fz) ≠ 0 := fun hd => hz0 ((eq_of_dec _ 0 hzp p384_pos).mpr (by rw [hd]; simp))
    simp [this] at hn

theorem dec_one : dec (2 ^ 384 % p384) = 1 := by
  rw [dec, cast_mod_p, mul_comm]; exact rinv_cast

/-- A pair of coordinates represents the point their values name. -/
theorem rep2_dec (P : nist.Point) (xy : Nat × Nat) (h : p384Represents2 P xy) :
    xy.1 < p384 ∧ xy.2 < p384 ∧ P = some ((dec xy.1).val, (dec xy.2).val) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [← h3, val_dec, val_dec]⟩

/-- `from_affine` of an affine point holds the point it represents. -/
theorem from_affine_jrep_spec (p : mid.p384.AffineMontPoint) (P : nist.Point)
    (h : p384Represents2 P (pairNat6 p.xy.val)) :
    mid.p384.JacobianMontPoint.from_affine p ⦃ pt => jrep P pt ⦄ := by
  apply WP.spec_mono (from_affine_spec p)
  intro pt hpt
  obtain ⟨h1, h2, h3⟩ := h
  rw [jrep, hpt, CURVE_ONE_MONT_val]
  exact represents_of_represents2 P _ _ ⟨h1, h2, h3⟩

@[step]
theorem double_spec (_hr : Runs) (pt : mid.p384.JacobianMontPoint) (P : nist.Point) (h : jrep P pt) :
    mid.p384.JacobianMontPoint.double pt ⦃ r => jrep (p384Add P P) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.double mid.p384.JacobianMontPoint.zero
  step*
  exact a_post P h

theorem add_affine_ne_spec (_hr : Runs) (pt : mid.p384.JacobianMontPoint) (p : mid.p384.AffineMontPoint)
    (P1 P2 : nist.Point) (h1 : jrep P1 pt) (h2 : p384Represents2 P2 (pairNat6 p.xy.val)) (hne : P1 ≠ P2) :
    mid.p384.JacobianMontPoint.add_affine pt p ⦃ r => jrep (p384Add P1 P2) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.add_affine
  step as ⟨inf, hinf⟩
  step as ⟨a, ha⟩
  exact ha P1 P2 h1 h2 hne

@[step]
theorem jac_add_spec (_hr : Runs) (pt q : mid.p384.JacobianMontPoint) (P1 P2 : nist.Point) (h1 : jrep P1 pt)
    (h2 : jrep P2 q) (hne : P1 = P2 → P2 = none) :
    mid.p384.JacobianMontPoint.add pt q ⦃ r => jrep (p384Add P1 P2) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.add
  step*
  exact a_post P1 P2 h1 h2 hne

theorem onCurve_zmod (x y : Nat) (h : p384OnCurve (some (x, y))) :
    (y : ZMod p384) ^ 2 = (x : ZMod p384) ^ 3 + ((p384 - 3 : Nat) : ZMod p384) * x + (b384 : ZMod p384) := by
  obtain ⟨-, -, h⟩ := h
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
  push_cast at this
  exact this

/-- Two points of the curve with the same x and different y are opposite. -/
theorem neg_of_same_x (x y1 y2 : Nat) (h1 : p384OnCurve (some (x, y1))) (h2 : p384OnCurve (some (x, y2)))
    (hne : y1 ≠ y2) : some (x, y2) = p384Neg (some (x, y1)) := by
  have e1 := onCurve_zmod x y1 h1
  have e2 := onCurve_zmod x y2 h2
  have hne' : (y2 : ZMod p384) - y1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h2.2.1, Nat.mod_eq_of_lt h1.2.1] at h
    exact hne h.symm
  have hsum : (y2 : ZMod p384) + y1 = 0 := by
    have : ((y2 : ZMod p384) - y1) * ((y2 : ZMod p384) + y1) = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.mp this).resolve_left hne'
  simp only [p384Neg, nist.neg, Option.some.injEq, Prod.mk.injEq, true_and]
  have hlt : (p384 - y1 % p384) % p384 < p384 := Nat.mod_lt _ p384_pos
  rw [← Nat.mod_eq_of_lt h2.2.1, ← Nat.mod_eq_of_lt hlt, ← ZMod.natCast_eq_natCast_iff', nist.natCast_neg_mod]
  linear_combination hsum

theorem val_inj (a b : ZMod p384) : a.val = b.val ↔ a = b := ⟨fun h => ZMod.val_injective _ h, fun h => h ▸ rfl⟩

/-- `public_add_affine`: the sum, for any points, which settles points
sharing x, equal or opposite, before `p384_montjmixadd`, whose contract
excludes only equal points. -/
@[step]
theorem add_affine_spec (_hr : Runs) (pt : mid.p384.JacobianMontPoint) (p : mid.p384.AffineMontPoint)
    (P1 P2 : nist.Point) (hc1 : p384OnCurve P1) (hc2 : p384OnCurve P2) (h1 : jrep P1 pt)
    (h2 : p384Represents2 P2 (pairNat6 p.xy.val)) :
    mid.p384.JacobianMontPoint.public_add_affine pt p ⦃ r => jrep (p384Add P1 P2) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_add_affine
  step with is_infinity_spec pt P1 h1 as ⟨b, hb⟩
  split
  · rename_i hbt
    rw [hb.mp hbt]
    step with from_affine_jrep_spec p P2 h2 as ⟨r, hr⟩
    rw [p384Laws.mul_none P2 hc2]; exact hr
  · rename_i hbf
    have hP1 : P1 ≠ none := fun h => hbf (hb.mpr h)
    obtain ⟨hpx, hpy, hP2⟩ := rep2_dec P2 _ h2
    obtain ⟨hX, hY, hZ, hP1eq⟩ := h1
    rw [ofJacobian_dec] at hP1eq
    set X := (tripleNat6 pt.xyz.val).1
    set Y := (tripleNat6 pt.xyz.val).2.1
    set Z := (tripleNat6 pt.xyz.val).2.2
    have hZ0 : dec Z ≠ 0 := fun h => hP1 (by rw [← hP1eq, ite_eq_left h])
    rw [ite_eq_right hZ0] at hP1eq
    set px := (pairNat6 p.xy.val).1
    set py := (pairNat6 p.xy.val).2
    have hlt : ∀ x, x % p384 < p384 := fun x => Nat.mod_lt _ p384_pos
    step as ⟨fz, hfzZ⟩
    step with mont_sqr_spec _hr fz (by rw [hfzZ]; exact hZ) as ⟨z2, hz2⟩
    step as ⟨fe1, hfe1x⟩
    step with mont_mul_spec _hr fe1 z2 (by rw [hfe1x]; exact hpx) (by rw [hz2]; exact hlt _) as ⟨fe2, hfe2⟩
    step as ⟨fe3, hfe3X⟩
    step as ⟨b1, hb1⟩
    have hxeq : b1 ↔ (dec px).val = (dec X * (dec Z ^ 2)⁻¹).val := by
      rw [hb1, hfe3X, eq_of_dec _ _ (by rw [hfe2]; exact hlt _) hX, hfe2, dec_mont_mul, hz2,
        dec_mont_sqr, hfzZ, hfe1x, val_inj, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hZ0)]
    split
    · rename_i hb1t
      have hxe := hxeq.mp hb1t
      step as ⟨fe4, hfe4y⟩
      step with mont_mul_spec _hr z2 fz (by rw [hz2]; exact hlt _) (by rw [hfzZ]; exact hZ) as ⟨fe5, hfe5⟩
      step with mont_mul_spec _hr fe4 fe5 (by rw [hfe4y]; exact hpy) (by rw [hfe5]; exact hlt _) as ⟨fe6, hfe6⟩
      step as ⟨fe7, hfe7Y⟩
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
        have hneg : P2 = p384Neg P1 := by
          have hc1' := hc1
          have hc2' := hc2
          rw [← hP1eq, ← hxe] at hc1'
          rw [hP2] at hc2'
          rw [← hP1eq, hP2, ← hxe]
          refine neg_of_same_x _ _ _ hc1' hc2' ?_
          intro h; exact hb2f (hyeq.mpr h.symm)
        step as ⟨r, hr⟩
        rw [hneg, p384Laws.mul_neg P1 hc1]; exact hr
    · rename_i hb1f
      have hne : P1 ≠ P2 := by
        rw [← hP1eq, hP2]
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact hb1f (hxeq.mpr h.1.symm)
      step with add_affine_ne_spec _hr pt p P1 P2 ⟨hX, hY, hZ, by rw [ofJacobian_dec, ite_eq_right hZ0, hP1eq]⟩ h2 hne
        as ⟨r, hr⟩
      exact hr

/-! ## Non-adjacent form, `mid::util::public_naf`, which `Rind.X86_64.Naf` proves -/

@[step]
theorem scalar_naf_spec (W : U32) (hW : W.val = 5 ∨ W.val = 6) (s : mid.p384.Scalar) :
    mid.p384.Scalar.public_naf W s ⦃ ds =>
      nafVal ds.val = scNat s ∧ ∀ j < 385, nafDigit (2 ^ (W.val - 1)) (ds.val[j]!).val ⦄ := by
  unfold mid.p384.Scalar.public_naf
  step as ⟨sl, hsl⟩
  step as ⟨s1, back, hs1, hback⟩
  step with naf_spec W hW sl 384 (by rw [hsl]; simp) (by norm_num) (by rw [hsl]; simp) s1
      (by rw [Slice.length, hs1]; exact (Array.repeat 385#usize 0#i8).property) as
    ⟨s2, hl2, hv2, hd2⟩
  have hv : (back s2).val = s2.val := by
    rw [hback]; exact Array.from_slice_val _ _ (by simpa [Slice.length] using hl2)
  rw [hv, hsl] at *
  exact ⟨by simpa [Array.val_to_slice] using hv2, hd2⟩

theorem neg_val (v : ZMod p384) : (p384 - v.val % p384) % p384 = (-v).val := by
  have h := nist.natCast_neg_mod (p := p384) v.val
  rw [ZMod.natCast_val, ZMod.cast_id', id] at h
  rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ p384_pos)]

theorem dec_neg (y : Nat) (hy : y < p384) : dec ((p384 - y) % p384) = -(dec y) := by
  have := nist.natCast_neg_mod (p := p384) y
  rw [Nat.mod_eq_of_lt hy] at this
  simp only [dec]; rw [this]; ring

/-- `negate_y`: the point's opposite, `p384Neg`. -/
@[step]
theorem negate_y_spec (pt : mid.p384.AffineMontPoint) (P : nist.Point)
    (h : p384Represents2 P (pairNat6 pt.xy.val)) :
    mid.p384.AffineMontPoint.negate_y pt ⦃ r => p384Represents2 (p384Neg P) (pairNat6 r.xy.val) ⦄ := by
  unfold mid.p384.AffineMontPoint.negate_y
  have hl : (pt.xy.val).length = 12 := pt.xy.property
  obtain ⟨hx, hy, rfl⟩ := rep2_dec P _ h
  step as ⟨fy, hfyv⟩
  step with fe_negate_spec fy (by rw [hfyv]; omega) as ⟨ny, hny⟩
  step*
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [s_post1, s1_post, mid.p384.AffineMontPoint.Y]
  · have hny' : ny.val.length = 6 := ny.property
    have hv : (index_mut_back s2).val = pt.xy.val.take 6 ++ ny.val := by
      rw [s_post2, s2_post, s1_post, Array.val_to_slice]
      simp only [mid.p384.AffineMontPoint.Y]
      generalize pt.xy.val = l at hl ⊢
      match l, hl with
      | [a, b, c, d, e, f, g, h', i, j, k, m], _ =>
        generalize ny.val = q at hny' ⊢
        match q, hny' with
        | [a', b', c', d', e', f'], _ => simp [List.setSlice!]
    rw [hv, pairNat6_append _ _ (by simp [hl]) hny']
    simp only [p384Neg]
    refine ⟨by simpa [pairNat6] using hx, ?_, ?_⟩
    · rw [show wordsNat ny.val = feNat ny from rfl, hny]; exact Nat.mod_lt _ p384_pos
    · congr 2
      · rw [val_dec]; simp [pairNat6]
      · rw [show wordsNat ny.val = feNat ny from rfl, hny, hfyv, neg_val]
        dsimp only
        rw [val_dec, dec_neg _ hy]

/-! ## Twin multiplication, `JacobianMontPoint::public_twin_multiply` -/

theorem lookup_spec (table : Std.Array U64 192#usize) (idx : U8) (h1 : 1 ≤ idx.val) (h16 : idx.val ≤ 16) :
    mid.p384.AffineMontPoint.public_lookup_comb table idx ⦃ pt =>
      pairNat6 pt.xy.val = pairNat6 (table.val.drop (12 * (idx.val - 1))) ⦄ := by
  unfold mid.p384.AffineMontPoint.public_lookup_comb mid.p384.AffineMontPoint.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  have hi1v : i1.val = idx.val - 1 := by
    rw [i1_post, UScalar.cast_val_eq, i_post]; apply Nat.mod_eq_of_lt; scalar_tac
  have hs1l : s1.val.length = 12 := by
    have := s1_post1; simp only [Slice.length] at this; omega
  rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by simp [hs1l]), s1_post,
    Array.val_to_slice, i2_post, offs_post, hi1v]
  simp only [List.slice, Nat.add_sub_cancel_left, pairNat6_take12]
  rw [Nat.mul_comm]

instance : Inhabited mid.p384.AffineMontPoint := ⟨⟨Array.repeat 12#usize 0#u64⟩⟩

/-- `odd` holds Q's odd multiples from `base`: entry i is Q times 2i + base. -/
def OddMultiples (Q : nist.Point) (base : Nat) (odd : Std.Array mid.p384.AffineMontPoint 8#usize) : Prop :=
  ∀ i < 8, p384Represents2 (p384Pow Q (2 * i + base)) (pairNat6 (odd.val[i]!).xy.val)

/-- The point a nonzero digit names, as the twin multiplication looks it up. -/
theorem digit_point (P : nist.Point) (hP : p384OnCurve P) (d : I8) (pt : mid.p384.AffineMontPoint)
    (hpt : p384Represents2 (p384Pow P d.val.natAbs) (pairNat6 pt.xy.val)) :
    (if d < 0#i8 then mid.p384.AffineMontPoint.negate_y pt else ok pt) ⦃ r =>
      p384Represents2 (p384ZPow P d.val) (pairNat6 r.xy.val) ⦄ := by
  split
  · rename_i hneg
    have hneg' : d.val < 0 := by simpa using (IScalar.lt_equiv _ _).mp hneg
    apply WP.spec_mono (negate_y_spec pt _ hpt)
    intro r hr
    rwa [← P384Laws.zpow_natCast, p384Laws.neg_zpow P hP, show -(d.val.natAbs : Int) = d.val by omega] at hr
  · rename_i hpos
    have hpos' : ¬ d.val < 0 := fun h => hpos ((IScalar.lt_equiv _ _).mpr (by simpa using h))
    simp only [WP.spec_ok]
    rwa [← P384Laws.zpow_natCast, show (d.val.natAbs : Int) = d.val by omega] at hpt

/-- `row` holds G to 16G, as the first comb table does. -/
def GRow (row : Std.Array U64 192#usize) : Prop :=
  ∀ d, 1 ≤ d → d ≤ 16 → p384Represents2 (p384Pow p384G d) (pairNat6 (row.val.drop (12 * (d - 1))))

theorem twin_loop_spec (_hr : Runs) (Q : nist.Point) (hQ : p384OnCurve Q)
    (odd : Std.Array mid.p384.AffineMontPoint 8#usize) (hodd : OddMultiples Q 1 odd)
    (more : Option (Std.Array mid.p384.AffineMontPoint 8#usize))
    (hmore : ∀ m, more = some m → OddMultiples Q 17 m)
    (g p : Std.Array I8 385#usize) (hg : ∀ j < 385, nafDigit 16 (g.val[j]!).val)
    (hp : ∀ j < 385, nafDigit (if more = none then 16 else 32) (p.val[j]!).val)
    (gm : Std.Array U64 192#usize) (hgm : GRow gm)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (hs : iter.iter.start.val = 0)
    (he : iter.iter.end.val ≤ 385) (result : mid.p384.JacobianMontPoint)
    (hres : jrep (twin384 p384G Q (nafVal (g.val.drop iter.iter.end.val)) (nafVal (p.val.drop iter.iter.end.val)))
      result) :
    mid.p384.JacobianMontPoint.public_twin_multiply_loop iter odd more g p gm result ⦃ r =>
      jrep (twin384 p384G Q (nafVal g.val) (nafVal p.val)) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_twin_multiply_loop
  have hGc := p384OnCurve_G
  apply loop.spec_decr_nat (fun x => x.1.iter.end.val)
    (fun x => x.1.iter.start.val = 0 ∧ x.1.iter.end.val ≤ 385 ∧ x.2.1 = more ∧
      jrep (twin384 p384G Q (nafVal (g.val.drop x.1.iter.end.val)) (nafVal (p.val.drop x.1.iter.end.val))) x.2.2)
  · rintro ⟨it, m1, res⟩ ⟨hs, he, hm1, hres⟩
    simp only at hs he hm1 hres ⊢
    rw [hm1]
    unfold mid.p384.JacobianMontPoint.public_twin_multiply_loop.body
    step as ⟨o, it1, hst, ho⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, he1⟩ := ho
      simp only
      set A := nafVal (g.val.drop it.iter.end.val)
      set B := nafVal (p.val.drop it.iter.end.val)
      have hi : it1.iter.end.val < 385 := by omega
      have hgl : g.val.length = 385 := g.property
      have hpl : p.val.length = 385 := p.property
      step as ⟨gd, hgd⟩
      step as ⟨pd, hpd⟩
      have hgd' : gd = g.val[it1.iter.end.val]! := by rw [hgd, getElem_eq_getElem! _ _ (by omega)]
      have hpd' : pd = p.val[it1.iter.end.val]! := by rw [hpd, getElem_eq_getElem! _ _ (by omega)]
      step with is_infinity_spec res _ hres as ⟨b, hb⟩
      have hT := p384Laws.twin_onCurve p384G Q hGc hQ
      apply WP.spec_bind (Pₘ := fun r1 => jrep (twin384 p384G Q (2 * A) (2 * B)) r1)
      · split
        · rename_i hbt
          simp only [WP.spec_ok]
          have h0 := hb.mp hbt
          rw [← p384Laws.twin_double p384G Q hGc hQ, h0, p384Laws.mul_none none trivial, ← h0]
          exact hres
        · step with double_spec _hr res _ hres as ⟨r1, hr1⟩
          rwa [p384Laws.twin_double p384G Q hGc hQ] at hr1
      intro r1 hr1
      apply WP.spec_bind (Pₘ := fun x : Option (Std.Array mid.p384.AffineMontPoint 8#usize) ×
          mid.p384.JacobianMontPoint => x.1 = more ∧ jrep (twin384 p384G Q (2 * A) (2 * B + pd.val)) x.2)
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
          obtain ⟨hodd', hlt'⟩ := P256.i8_natAbs pd _ hA' hdig hpv
          step as ⟨i1, hi1⟩
          step as ⟨i2, hi2⟩
          simp only [lift, bind_ok]
          generalize hi3 : core.convert.num.FromUsizeU8.from i2 = i3
          have hi3v : i3.val = pd.val.natAbs / 2 := by
            rw [← hi3, core.convert.num.FromUsizeU8.from_val_eq, hi2, hi1]
          have h2i3 : 2 * i3.val + 1 = pd.val.natAbs := by omega
          apply WP.spec_bind (Pₘ := fun tmp : mid.p384.AffineMontPoint =>
            p384Represents2 (p384Pow Q pd.val.natAbs) (pairNat6 tmp.xy.val))
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
          step with add_affine_spec _hr r1 tmp1 _ _ (hT _ _) (p384Laws.zpow_onCurve Q hQ _) hr1 htmp1 as ⟨r3, hr3⟩
          rw [p384Laws.twin_add_right p384G Q hGc hQ] at hr3
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
      have hfin : ∀ r, jrep (twin384 p384G Q (2 * A + gd.val) (2 * B + pd.val)) r →
          it1.iter.start.val = 0 ∧ it1.iter.end.val ≤ 385 ∧
            jrep (twin384 p384G Q (nafVal (g.val.drop it1.iter.end.val)) (nafVal (p.val.drop it1.iter.end.val))) r ∧
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
        obtain ⟨hodd', hlt'⟩ := P256.i8_natAbs gd 16 (by simp) hdig hgv
        step as ⟨i1, hi1⟩
        step with lookup_spec gm i1 (by rw [hi1]; omega) (by rw [hi1]; simp at hlt'; omega) as ⟨tmp, htmp⟩
        have htab0 := hgm i1.val (by rw [hi1]; omega) (by rw [hi1]; simp at hlt'; omega)
        have hrep : p384Represents2 (p384Pow p384G gd.val.natAbs) (pairNat6 tmp.xy.val) := by
          rw [htmp, ← hi1]; exact htab0
        step with digit_point p384G hGc gd tmp hrep as ⟨tmp1, htmp1⟩
        step with add_affine_spec _hr r2 tmp1 _ _ (hT _ _) (p384Laws.zpow_onCurve p384G hGc _) hr2 htmp1 as
          ⟨r3, hr3⟩
        rw [p384Laws.twin_add_left p384G Q hGc hQ] at hr3
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

/-- The first comb table holds G to 16G. -/
theorem first_row : GRow (mid.p384.precomp.CURVE_GENERATOR_PRECOMP_COMB.val[0]!) := by
  intro d hd1 hd
  have := tabulated 0 (by norm_num) d hd1 hd
  simpa using this

theorem twin_multiply_spec (_hr : Runs) (g p : mid.p384.Scalar) (Q : nist.Point)
    (hQ : p384OnCurve Q) (odd : Std.Array mid.p384.AffineMontPoint 8#usize) (hodd : OddMultiples Q 1 odd)
    (more : Option (Std.Array mid.p384.AffineMontPoint 8#usize))
    (hmore : ∀ m, more = some m → OddMultiples Q 17 m) :
    mid.p384.JacobianMontPoint.public_twin_multiply g p odd more ⦃ r =>
      jrep (twin384 p384G Q (scNat g) (scNat p)) r ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_twin_multiply
  step with scalar_naf_spec 5#u32 (by simp) g as ⟨gd, hgv, hgd⟩
  apply WP.spec_bind (Pₘ := fun pd : Std.Array I8 385#usize => nafVal pd.val = scNat p ∧
    ∀ j < 385, nafDigit (if more = none then 16 else 32) (pd.val[j]!).val)
  · rcases more with _ | m
    · simp only
      apply WP.spec_mono (scalar_naf_spec 5#u32 (by simp) p)
      intro pd hpd; simpa using hpd
    · simp only
      apply WP.spec_mono (scalar_naf_spec 6#u32 (by simp) p)
      intro pd hpd; simpa using hpd
  intro pd ⟨hpv, hpd⟩
  step as ⟨a1, ha1⟩
  step*
  have hgl : gd.val.length = 385 := gd.property
  have hpl : pd.val.length = 385 := pd.property
  have hend : iter.iter.end.val = 385 := by rw [iter_post]; simp [s_post, Slice.len, hgl]
  have hrow : GRow a1 := by
    rw [ha1, getElem_eq_getElem! _ _ (by simp)]; exact first_row
  apply WP.spec_mono (twin_loop_spec _hr Q hQ odd hodd more hmore gd pd (by simpa using hgd) hpd a1
    hrow iter (by rw [iter_post]; rfl)
    (by omega) result (by
      rw [hend, List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
      simp only [nafVal]
      rw [p384Laws.twin_zero p384G Q p384OnCurve_G hQ]; exact result_post))
  intro r hr
  rwa [hgv, hpv] at hr

/-! ## The x-coordinate check, `JacobianMontPoint::public_x_is` -/

theorem x_is_loop_spec (a : Std.Array U64 6#usize) (iter : core.ops.range.Range Usize)
    (rpn : Std.Array U64 6#usize) (carry : Bool) (hs : iter.start.val ≤ 6) (he : iter.end.val = 6)
    (hinv : wordsNat (rpn.val.take iter.start.val) + 2 ^ (64 * iter.start.val) * carry.toNat =
      wordsNat (a.val.take iter.start.val) + wordsNat (mid.p384.CURVE_ORDER.val.take iter.start.val)) :
    mid.p384.JacobianMontPoint.public_x_is_loop iter a rpn carry ⦃ r =>
      wordsNat r.1.val + 2 ^ 384 * r.2.toNat = wordsNat a.val + n384 ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_x_is_loop
  have hal : a.val.length = 6 := a.property
  have hnl : mid.p384.CURVE_ORDER.val.length = 6 := mid.p384.CURVE_ORDER.property
  apply loop.spec_decr_nat (fun x => 6 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 6 ∧
      wordsNat (x.2.1.val.take x.1.start.val) + 2 ^ (64 * x.1.start.val) * x.2.2.toNat =
        wordsNat (a.val.take x.1.start.val) + wordsNat (mid.p384.CURVE_ORDER.val.take x.1.start.val))
  · rintro ⟨it, r, c⟩ ⟨hs, he, hinv⟩
    simp only at hs he hinv ⊢
    unfold mid.p384.JacobianMontPoint.public_x_is_loop.body
    have hrl : r.val.length = 6 := r.property
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
      have hi6 : it.start.val < 6 := by omega
      have hal1 : (a1.val).length = 6 := a1.property
      have hset : a1.val = r.val.set it.start.val s1 := by rw [ha1, Std.Array.set_val_eq]
      rw [hst, P256.wordsNat_take_succ _ _ (by omega), P256.wordsNat_take_succ _ _ (by omega),
        P256.wordsNat_take_succ _ _ (by omega)]
      have htk : a1.val.take it.start.val = r.val.take it.start.val := by
        rw [hset, List.take_set_of_le (by omega)]
      have hgi : (a1.val[it.start.val]!) = s1 := by
        rw [hset]; simp [hrl, hi6]
      rw [htk, hgi, ← getElem_eq_getElem! _ _ (by omega), ← getElem_eq_getElem! _ _ (by omega), ← hi1, ← hi2,
        show 64 * (it.start.val + 1) = 64 * it.start.val + 64 by ring, pow_add]
      have e : 2 ^ (64 * it.start.val) * s1.val + 2 ^ (64 * it.start.val) * 2 ^ 64 * (c1 || c2).toNat =
          2 ^ (64 * it.start.val) * (i1.val + i2.val + c.toNat) := by rw [← hsum]; ring
      linear_combination e + hinv
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have h6 : it.start.val = 6 := by omega
      rw [h6, List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.take_of_length_le (by omega), CURVE_ORDER_val] at hinv
      exact hinv
  · exact ⟨hs, he, hinv⟩

theorem dec_tomont (v : Nat) : dec (2 ^ 384 * v % p384) = v := by
  simp only [dec, cast_mod_p, Nat.cast_mul]
  rw [← mul_assoc, mul_comm (p384RInv : ZMod p384), rinv_cast, one_mul]

theorem x_is_closure_spec (_hr : Runs) (pt : mid.p384.JacobianMontPoint) (z2 : mid.p384.FieldElement) (x : Nat)
    (hx : x < p384) (hX : (tripleNat6 pt.xyz.val).1 < p384) (hz2 : feNat z2 < p384)
    (heq : ∀ v : Nat, dec (feNat z2) * v = dec (tripleNat6 pt.xyz.val).1 ↔ (v : ZMod p384) = x)
    (v : Std.Array U64 6#usize) :
    mid.p384.JacobianMontPoint.public_x_is.closure.Insts.CoreOpsFunctionFnTupleArrayU646Bool.call (z2, pt) v
      ⦃ b => b ↔ wordsNat v.val % p384 = x ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_x_is.closure.Insts.CoreOpsFunctionFnTupleArrayU646Bool.call
  step with as_mont_spec _hr v as ⟨fe1, hfe1⟩
  step with mont_mul_spec _hr fe1 z2 (by rw [hfe1]; exact Nat.mod_lt _ p384_pos) hz2 as ⟨fe2, hfe2⟩
  step as ⟨fe3, hfe3X⟩
  step as ⟨b, hb⟩
  rw [hb, hfe3X, eq_of_dec _ _ (by rw [hfe2]; exact Nat.mod_lt _ p384_pos) hX, hfe2, dec_mont_mul, hfe1,
    dec_tomont, mul_comm, heq, ← cast_mod_p, ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.mod_eq_of_lt hx]

theorem p384_lt_two_n : p384 < 2 * n384 := by unfold p384 n384; decide
theorem n384_lt_p384 : n384 < p384 := by unfold p384 n384; decide

theorem x_is_spec (_hr : Runs) (pt : mid.p384.JacobianMontPoint) (x y : Nat) (h : jrep (some (x, y)) pt)
    (r : mid.p384.Scalar) (hr : scNat r < n384) :
    mid.p384.JacobianMontPoint.public_x_is pt r ⦃ b => b ↔ x % n384 = scNat r ⦄ := by
  obtain ⟨hX, hY, hZ, hP⟩ := h
  rw [ofJacobian_dec] at hP
  set X := (tripleNat6 pt.xyz.val).1
  set Z := (tripleNat6 pt.xyz.val).2.2
  have hZ0 : dec Z ≠ 0 := fun h0 => by rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)] at hP; cases hP
  rw [ite_eq_right_iff.mpr (fun h => absurd h hZ0)] at hP
  simp only [Option.some.injEq, Prod.mk.injEq] at hP
  obtain ⟨hxv, -⟩ := hP
  have hx : x < p384 := by rw [← hxv]; exact ZMod.val_lt _
  unfold mid.p384.JacobianMontPoint.public_x_is
  step as ⟨fz, hfzZ⟩
  step with mont_sqr_spec _hr fz (by rw [hfzZ]; exact hZ) as ⟨z2, hz2⟩
  have hz2p : feNat z2 < p384 := by rw [hz2]; exact Nat.mod_lt _ p384_pos
  have heq : ∀ v : Nat, dec (feNat z2) * v = dec X ↔ (v : ZMod p384) = x := by
    intro v
    rw [hz2, dec_mont_sqr, hfzZ, ← hxv, ZMod.natCast_val, ZMod.cast_id', id,
      eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hZ0), mul_comm]
  have hrp : scNat r < p384 := lt_trans hr n384_lt_p384
  have hp2n := p384_lt_two_n
  have hmod : x % n384 = scNat r ↔ x = scNat r ∨ x = scNat r + n384 := by
    constructor
    · intro h
      by_cases hxn : x < n384
      · left; rw [← h, Nat.mod_eq_of_lt hxn]
      · right; rw [← h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rintro (rfl | rfl)
      · exact Nat.mod_eq_of_lt hr
      · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  step with x_is_closure_spec _hr pt z2 x hx hX hz2p heq r as ⟨b, hb⟩
  rw [show wordsNat r.val % p384 = scNat r from Nat.mod_eq_of_lt hrp] at hb
  rw [hmod]
  split
  · rename_i hbt
    simp only [WP.spec_ok, true_iff]
    exact Or.inl (hb.mp hbt).symm
  · rename_i hbf
    have hxr : x ≠ scNat r := fun h => hbf (hb.mpr h.symm)
    step with x_is_loop_spec r { start := 0#usize, «end» := 6#usize } (Array.repeat 6#usize 0#u64) false
      (by simp) (by simp) (by simp [wordsNat]) as ⟨rpn, carry, hrpn⟩
    split
    · rename_i hc
      simp only [hc, Bool.toNat_true, Nat.mul_one] at hrpn
      rw [WP.spec_ok]
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rintro (h | h)
      · exact absurd h hxr
      · have hp := p384_lt
        simp only [scNat] at h hrpn
        generalize (2 : Nat) ^ 384 = M at *
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
theorem jrep_some (P : nist.Point) (pt : mid.p384.JacobianMontPoint) (h : jrep P pt) (hne : P ≠ none) :
    (tripleNat6 pt.xyz.val).1 < p384 ∧ (tripleNat6 pt.xyz.val).2.1 < p384 ∧ (tripleNat6 pt.xyz.val).2.2 < p384 ∧
      dec (tripleNat6 pt.xyz.val).2.2 ≠ 0 ∧
      P = some ((dec (tripleNat6 pt.xyz.val).1 * (dec (tripleNat6 pt.xyz.val).2.2 ^ 2)⁻¹).val,
        (dec (tripleNat6 pt.xyz.val).2.1 * (dec (tripleNat6 pt.xyz.val).2.2 ^ 3)⁻¹).val) := by
  obtain ⟨hX, hY, hZ, hP⟩ := h
  rw [ofJacobian_dec] at hP
  have hZ0 : dec (tripleNat6 pt.xyz.val).2.2 ≠ 0 := fun h0 => by
    rw [ite_eq_left_iff.mpr (fun h => absurd h0 h)] at hP; exact hne hP.symm
  rw [ite_eq_right_iff.mpr (fun h => absurd h hZ0)] at hP
  exact ⟨hX, hY, hZ, hZ0, hP.symm⟩

theorem as_affine_by_spec (_hr : Runs) (pt : mid.p384.JacobianMontPoint) (P : nist.Point) (h : jrep P pt) (hne : P ≠ none)
    (zi : mid.p384.FieldElement) (hzi : feNat zi < p384)
    (hinv : dec (feNat zi) = (dec (tripleNat6 pt.xyz.val).2.2)⁻¹) :
    mid.p384.JacobianMontPoint.as_affine_by pt zi ⦃ a => p384Represents2 P (pairNat6 a.xy.val) ⦄ := by
  obtain ⟨hX, hY, hZ, hZ0, rfl⟩ := jrep_some P pt h hne
  have hlt : ∀ x, x % p384 < p384 := fun x => Nat.mod_lt _ p384_pos
  unfold mid.p384.JacobianMontPoint.as_affine_by
  step with mont_sqr_spec _hr zi hzi as ⟨z2, hz2⟩
  step with mont_mul_spec _hr z2 zi (by rw [hz2]; exact hlt _) hzi as ⟨z3, hz3⟩
  step as ⟨fx, hfxX⟩
  step with mont_mul_spec _hr fx z2 (by rw [hfxX]; exact hX) (by rw [hz2]; exact hlt _) as ⟨x, hx⟩
  step as ⟨fy, hfyY⟩
  step with mont_mul_spec _hr fy z3 (by rw [hfyY]; exact hY) (by rw [hz3]; exact hlt _) as ⟨y, hy⟩
  step as ⟨a, ha⟩
  rw [ha]
  refine ⟨by rw [hx]; exact hlt _, by rw [hy]; exact hlt _, ?_⟩
  rw [val_dec, val_dec, hx, hy,
    dec_mont_mul, dec_mont_mul, hz3, hz2, dec_mont_mul, dec_mont_sqr, hinv, hfxX, hfyY]
  congr 3 <;> field_simp

instance : Inhabited mid.p384.JacobianMontPoint := ⟨⟨Array.repeat 18#usize 0#u64⟩⟩

/-- The value of the z of point `j`. -/
abbrev zv (pts : Std.Array mid.p384.JacobianMontPoint 8#usize) (j : Nat) : ZMod p384 :=
  dec (tripleNat6 (pts.val[j]!).xyz.val).2.2

theorem batch_loop0_spec (_hr : Runs) (pts : Std.Array mid.p384.JacobianMontPoint 8#usize)
    (hz : ∀ j < 8, (tripleNat6 (pts.val[j]!).xyz.val).2.2 < p384)
    (iter : core.ops.range.Range Usize) (pre : Std.Array mid.p384.FieldElement 8#usize)
    (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8) (he : iter.end.val = 8)
    (hpre : ∀ j < iter.start.val, feNat (pre.val[j]!) < p384 ∧ dec (feNat (pre.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t) :
    mid.p384.JacobianMontPoint.public_batch_as_affine_loop0 iter pts pre ⦃ r =>
      ∀ j < 8, feNat (r.val[j]!) < p384 ∧ dec (feNat (r.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_batch_as_affine_loop0
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧ x.1.end.val = 8 ∧
      ∀ j < x.1.start.val, feNat (x.2.val[j]!) < p384 ∧ dec (feNat (x.2.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t)
  · rintro ⟨it, pr⟩ ⟨hs1, hs, he, hpr⟩
    simp only at hs1 hs he hpr ⊢
    unfold mid.p384.JacobianMontPoint.public_batch_as_affine_loop0.body
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
      have hfzv : feNat fz = (tripleNat6 (pts.val[it.start.val - 1]!).xyz.val).2.2 := by
        rw [hfz, hjmp']
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
        refine ⟨Nat.mod_lt _ p384_pos, ?_⟩
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

theorem zv_ne_zero (pts : Std.Array mid.p384.JacobianMontPoint 8#usize) (Ps : Nat → nist.Point)
    (h : ∀ j < 8, jrep (Ps j) (pts.val[j]!) ∧ Ps j ≠ none) (j : Nat) (hj : j < 8) : zv pts j ≠ 0 :=
  (jrep_some _ _ (h j hj).1 (h j hj).2).2.2.2.1

theorem batch_loop1_spec (_hr : Runs) (pts : Std.Array mid.p384.JacobianMontPoint 8#usize) (Ps : Nat → nist.Point)
    (h : ∀ j < 8, jrep (Ps j) (pts.val[j]!) ∧ Ps j ≠ none) (pre : Std.Array mid.p384.FieldElement 8#usize)
    (hpre : ∀ j < 8, feNat (pre.val[j]!) < p384 ∧ dec (feNat (pre.val[j]!)) = ∏ t ∈ Finset.range j, zv pts t)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (hs : iter.iter.start.val = 0)
    (he : iter.iter.end.val ≤ 8) (inv : mid.p384.FieldElement)
    (hinv : feNat inv < p384 ∧ dec (feNat inv) = (∏ t ∈ Finset.range iter.iter.end.val, zv pts t)⁻¹)
    (r : Std.Array mid.p384.AffineMontPoint 8#usize)
    (hr : ∀ j, iter.iter.end.val ≤ j → j < 8 → p384Represents2 (Ps j) (pairNat6 (r.val[j]!).xy.val)) :
    mid.p384.JacobianMontPoint.public_batch_as_affine_loop1 iter pts pre inv r ⦃ r' =>
      ∀ j < 8, p384Represents2 (Ps j) (pairNat6 (r'.val[j]!).xy.val) ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_batch_as_affine_loop1
  have hlt : ∀ x, x % p384 < p384 := fun x => Nat.mod_lt _ p384_pos
  apply loop.spec_decr_nat (fun x => x.1.iter.end.val)
    (fun x => x.1.iter.start.val = 0 ∧ x.1.iter.end.val ≤ 8 ∧
      (feNat x.2.1 < p384 ∧ dec (feNat x.2.1) = (∏ t ∈ Finset.range x.1.iter.end.val, zv pts t)⁻¹) ∧
      ∀ j, x.1.iter.end.val ≤ j → j < 8 → p384Represents2 (Ps j) (pairNat6 (x.2.2.val[j]!).xy.val))
  · rintro ⟨it, iv, rr⟩ ⟨hs, he, ⟨hivl, hiv⟩, hrr⟩
    simp only at hs he hivl hiv hrr ⊢
    unfold mid.p384.JacobianMontPoint.public_batch_as_affine_loop1.body
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
      have hzi : dec (feNat fe1) = (dec (tripleNat6 jmp.xyz.val).2.2)⁻¹ := by
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
      have hfzv : feNat fz = (tripleNat6 jmp.xyz.val).2.2 := hfz
      have hzl : feNat fz < p384 := by rw [hfzv]; exact (jrep_some _ _ hj1 hj2).2.2.1
      step with mont_mul_spec _hr iv fz hivl hzl as ⟨iv1, hiv1⟩
      have hiv1v : dec (feNat iv1) = (∏ t ∈ Finset.range i, zv pts t)⁻¹ := by
        rw [hiv1, dec_mont_mul, hiv, hfzv, ← he1, Finset.prod_range_succ, hjmp']
        have := zv_ne_zero pts Ps h i hi8
        have hp : ∏ t ∈ Finset.range i, zv pts t ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun t ht => zv_ne_zero pts Ps h t (by simp at ht; omega)
        field_simp
        try exact div_self this
      have hfin : ∀ j, i ≤ j → j < 8 → p384Represents2 (Ps j) (pairNat6 (a.val[j]!).xy.val) := by
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
      have hiv1l : feNat iv1 < p384 := by rw [hiv1]; exact hlt _
      exact ⟨hit1, by omega, hiv1l, hiv1v, hfin, by omega⟩
    · rw [ho]
      simp only [WP.spec_ok]
      intro j hj; exact hrr j (by omega) hj
  · exact ⟨hs, he, hinv, hr⟩

theorem batch_spec (_hr : Runs) (pts : Std.Array mid.p384.JacobianMontPoint 8#usize) (Ps : Nat → nist.Point)
    (h : ∀ j < 8, jrep (Ps j) (pts.val[j]!) ∧ Ps j ≠ none) :
    mid.p384.JacobianMontPoint.public_batch_as_affine pts ⦃ r =>
      ∀ j < 8, p384Represents2 (Ps j) (pairNat6 (r.val[j]!).xy.val) ⦄ := by
  unfold mid.p384.JacobianMontPoint.public_batch_as_affine
  have hlt : ∀ x, x % p384 < p384 := fun x => Nat.mod_lt _ p384_pos
  have hptl : pts.val.length = 8 := pts.property
  have hz : ∀ j < 8, (tripleNat6 (pts.val[j]!).xyz.val).2.2 < p384 := fun j hj => (h j hj).1.2.2.1
  step as ⟨sl, hsl⟩
  step with batch_loop0_spec _hr pts hz { start := 1#usize, «end» := Slice.len sl }
    (Array.repeat 8#usize mid.p384.CURVE_ONE_MONT) (by simp) (by simp) (by simp [hsl, Slice.len])
    (by
      intro j hj
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      have : (Array.repeat 8#usize mid.p384.CURVE_ONE_MONT).val[0]! = mid.p384.CURVE_ONE_MONT := by
        simp [Array.repeat]
      rw [this, CURVE_ONE_MONT_val, dec_one]
      exact ⟨hlt _, by simp⟩) as ⟨pre, hpre⟩
  step as ⟨fe, hfe⟩
  step as ⟨jmp, hjmp⟩
  step as ⟨fz, hfz⟩
  have hfe' : fe = pre.val[7]! := by rw [hfe, getElem_eq_getElem! _ _ (by simp)]
  have hjmp' : jmp = pts.val[7]! := by rw [hjmp, getElem_eq_getElem! _ _ (by simp)]
  have hfzv : feNat fz = (tripleNat6 (pts.val[7]!).xyz.val).2.2 := by rw [hfz, hjmp']
  obtain ⟨hfel, hfev⟩ := hpre 7 (by norm_num)
  rw [← hfe'] at hfel hfev
  step with mont_mul_spec _hr fe fz hfel (by rw [hfzv]; exact hz 7 (by norm_num)) as ⟨pr, hpr⟩
  have hprv : dec (feNat pr) = ∏ t ∈ Finset.range 8, zv pts t := by
    rw [hpr, dec_mont_mul, hfev, hfzv, Finset.prod_range_succ (fun t => zv pts t) 7]
  have hp8 : ∏ t ∈ Finset.range 8, zv pts t ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun t ht => zv_ne_zero pts Ps h t (by simp at ht; omega)
  step with demont_spec _hr pr (by rw [hpr]; exact hlt _) as ⟨f2, hf2⟩
  have hf2v : ((feNat f2 : Nat) : ZMod p384) = ∏ t ∈ Finset.range 8, zv pts t := by
    rw [hf2, cast_mod_p, ← hprv]; push_cast; rfl
  step as ⟨f3, hf3l, _, hf3⟩
  have hf2nz : feNat f2 % p384 ≠ 0 := by
    intro h0; apply hp8; rw [← hf2v, ← cast_mod_p, h0]; simp
  have hf3v : ((feNat f3 : Nat) : ZMod p384) = (∏ t ∈ Finset.range 8, zv pts t)⁻¹ := by
    have := congrArg (fun x : Nat => (x : ZMod p384)) (hf3 hf2nz)
    simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at this
    rw [← hf2v]; exact (inv_eq_of_mul_eq_one_right this).symm
  step with as_mont_spec _hr f3 as ⟨iv, hiv⟩
  simp only [mid.p384.AffineMontPoint.Insts.CoreDefaultDefault.default, core.default.DefaultArray.default,
    ]
  step as ⟨sl1, hsl1⟩
  step as ⟨it, hit⟩
  apply batch_loop1_spec _hr pts Ps h pre hpre it (by rw [hit]; rfl) (by rw [hit]; simp [hsl1, Slice.len])
    iv ⟨by rw [hiv]; exact hlt _, by rw [hiv, dec_tomont, hf3v, hit]; simp [hsl1, Slice.len]⟩
  intro j hj; rw [hit] at hj; simp [hsl1, Slice.len] at hj; omega

/-! ## A key's odd multiples, `AffineMontPoint::public_odd_multiples` -/

theorem n384_big : 64 < n384 := by unfold n384; decide

theorem odd_loop_spec (_hr : Runs) (Q : nist.Point) (hQ : p384OnCurve Q) (hQo : P384OrderOf Q)
    (p2 : mid.p384.JacobianMontPoint) (hp2 : jrep (p384ZPow Q 2) p2) (iter : core.ops.range.Range Usize)
    (m : Std.Array mid.p384.JacobianMontPoint 8#usize) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8)
    (he : iter.end.val = 8) (hm : ∀ j : Nat, j < iter.start.val → jrep (p384ZPow Q (2 * (j : Int) + 1)) (m.val[j]!)) :
    mid.p384.AffineMontPoint.public_odd_multiples_loop iter p2 m ⦃ r =>
      ∀ j : Nat, j < 8 → jrep (p384ZPow Q (2 * (j : Int) + 1)) (r.val[j]!) ⦄ := by
  unfold mid.p384.AffineMontPoint.public_odd_multiples_loop
  have hn := n384_big
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧ x.1.end.val = 8 ∧
      ∀ j : Nat, j < x.1.start.val → jrep (p384ZPow Q (2 * (j : Int) + 1)) (x.2.val[j]!))
  · rintro ⟨it, mm⟩ ⟨hs1, hs, he, hmm⟩
    simp only at hs1 hs he hmm ⊢
    unfold mid.p384.AffineMontPoint.public_odd_multiples_loop.body
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
      step with jac_add_spec _hr jmp p2 _ _ hj hp2 (fun h => absurd h (p384Laws.zpow_ne Q hQ hQo _ _
        (by omega) (by omega))) as ⟨s1, hs1'⟩
      rw [p384Laws.mul_zpow Q hQ] at hs1'
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

theorem odd_multiples_spec (_hr : Runs) (pt : mid.p384.AffineMontPoint) (Q : nist.Point)
    (hQ : p384OnCurve Q) (hQo : P384OrderOf Q) (h : p384Represents2 Q (pairNat6 pt.xy.val)) :
    mid.p384.AffineMontPoint.public_odd_multiples pt ⦃ m => OddMultiples Q 1 m ⦄ := by
  unfold mid.p384.AffineMontPoint.public_odd_multiples
  have hn := n384_big
  step with from_affine_jrep_spec pt Q h as ⟨p, hp⟩
  step with double_spec _hr p Q hp as ⟨p2, hp2⟩
  have hQ1 := p384Laws.zpow_one Q hQ
  rw [← hQ1, p384Laws.mul_zpow Q hQ] at hp2
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
  apply WP.spec_mono (batch_spec _hr m (fun j => p384ZPow Q (2 * j + 1))
    (fun j hj => ⟨hm j hj, p384Laws.zpow_ne_none Q hQ hQo _ (by omega) (by omega)⟩))
  intro r hr j hj
  have := hr j hj
  rwa [show (2 * (j : Int) + 1) = ((2 * j + 1 : Nat) : Int) by push_cast; ring, P384Laws.zpow_natCast] at this

/-- The odd multiples a key's cache builds: 17Q to 31Q, from its Q to 15Q. -/
theorem more_odd_spec (_hr : Runs) (Q : nist.Point) (hQ : p384OnCurve Q) (hQo : P384OrderOf Q)
    (odd : Std.Array mid.p384.AffineMontPoint 8#usize) (hodd : OddMultiples Q 1 odd) :
    mid.p384.AffineMontPoint.public_more_odd_multiples odd ⦃ m => OddMultiples Q 17 m ⦄ := by
  unfold mid.p384.AffineMontPoint.public_more_odd_multiples
  have hn := n384_big
  have hol : odd.val.length = 8 := odd.property
  have hz : ∀ k : Nat, p384Pow Q k = p384ZPow Q k := fun k => (P384Laws.zpow_natCast Q k).symm
  step as ⟨a7, ha7⟩
  have h7 := hodd 7 (by norm_num)
  rw [← getElem_eq_getElem! _ _ (by omega), ← ha7, hz] at h7
  step with from_affine_jrep_spec a7 _ h7 as ⟨p16, hp16⟩
  step as ⟨a0, ha0⟩
  have h0 := hodd 0 (by norm_num)
  rw [← getElem_eq_getElem! _ _ (by omega), ← ha0, hz] at h0
  step with add_affine_ne_spec _hr p16 a0 _ _ hp16 h0
    (p384Laws.zpow_ne Q hQ hQo _ _ (by norm_num) (by norm_num; omega)) as ⟨p161, hp161⟩
  rw [p384Laws.mul_zpow Q hQ] at hp161
  have hadd : ∀ x, mid.p384.JacobianMontPoint.add_affine p161 x ⦃ r =>
      ∀ k : Nat, 1 ≤ k → k ≤ 15 → p384Represents2 (p384ZPow Q k) (pairNat6 x.xy.val) →
        jrep (p384ZPow Q (16 + k)) r ⦄ := by
    intro x
    unfold mid.p384.JacobianMontPoint.add_affine
    step as ⟨inf, hinf⟩
    step as ⟨a, ha⟩
    intro k hk1 hk15 hrep
    have := ha _ _ hp161 hrep (p384Laws.zpow_ne Q hQ hQo _ _ (by omega) (by omega))
    rw [p384Laws.mul_zpow Q hQ] at this
    exact this
  step with P256.map_spec
    mid.p384.AffineMontPoint.public_more_odd_multiples.closure.Insts.CoreOpsFunctionFnMutTupleAffineMontPointJacobianMontPoint
    odd p161 (fun x r => ∀ k : Nat, 1 ≤ k → k ≤ 15 → p384Represents2 (p384ZPow Q k) (pairNat6 x.xy.val) →
      jrep (p384ZPow Q (16 + k)) r) (fun x _ => by
    simp only [mid.p384.AffineMontPoint.public_more_odd_multiples.closure.Insts.CoreOpsFunctionFnMutTupleAffineMontPointJacobianMontPoint.call_mut]
    step with hadd x as ⟨r, hr⟩
    exact hr) as ⟨l, hl⟩
  apply WP.spec_mono (batch_spec _hr l (fun j => p384ZPow Q (16 + (2 * j + 1))) (by
    intro j hj
    refine ⟨?_, p384Laws.zpow_ne_none Q hQ hQo _ (by omega) (by omega)⟩
    have hj' := hodd j hj
    rw [hz] at hj'
    exact hl j (by simpa using hj) (2 * j + 1) (by omega) (by omega) (by push_cast at hj' ⊢; exact hj')))
  intro r hr j hj
  have := hr j hj
  rwa [show (16 + (2 * (j : Int) + 1)) = ((2 * j + 17 : Nat) : Int) by push_cast; ring, ← hz] at this

/-! ## Raw verification, `VerifyingKey::raw_ecdsa_verify` -/

/-- A verifying key's caches of P, ..., 15P and 17P, ..., 31P, and a signing
key's cache of its encoded public key, whose atomics Aeneas cannot translate:
`ReuseCache::new` returns a cache, each cache holds only what its build
returns, built from the key's own point or scalar, which never changes after
the key is made, so whatever every such build's value satisfies,
`get_or_build_now`'s value does, and `get_or_build`'s, unless `None`, and a
clone, which copies a built value, returns. Reading P, ..., 15P to choose
aarch64's verification (`raw_ecdsa_verify`'s own build) returns too. P-384's
key check stores no encoding, so unlike P-256's this assumes nothing of other
builds. -/
structure Cached : Prop where
  new : ∃ c, low.generic.reuse_cache.ReuseCache.new
      (core.default.DefaultArray 8#usize mid.p384.AffineMontPoint.Insts.CoreDefaultDefault) = ok c
  get_or_build_now : ∀ (key : mid.p384.VerifyingKey) (P : Std.Array mid.p384.AffineMontPoint 8#usize → Prop),
    mid.p384.AffineMontPoint.public_odd_multiples key.point ⦃ P ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build_now
      (Array.Insts.CoreMarkerCopy 8#usize mid.p384.AffineMontPoint.Insts.CoreMarkerCopy)
      (core.default.DefaultArray 8#usize mid.p384.AffineMontPoint.Insts.CoreDefaultDefault)
      mid.p384.VerifyingKey.rind_ecdsa_verify.closure.Insts.CoreOpsFunctionFnOnceTupleArrayAffineMontPoint8
      key.odd_multiples key ⦃ P ⦄
  get_or_build : ∀ (key : mid.p384.VerifyingKey) (odd : Std.Array mid.p384.AffineMontPoint 8#usize)
      (P : Std.Array mid.p384.AffineMontPoint 8#usize → Prop),
    mid.p384.AffineMontPoint.public_odd_multiples key.point ⦃ o =>
      mid.p384.AffineMontPoint.public_more_odd_multiples o ⦃ P ⦄ ⦄ →
    mid.p384.AffineMontPoint.public_more_odd_multiples odd ⦃ P ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build
      (core.default.DefaultArray 8#usize mid.p384.AffineMontPoint.Insts.CoreDefaultDefault)
      mid.p384.VerifyingKey.rind_ecdsa_verify.closure_1.Insts.CoreOpsFunctionFnOnceTupleArrayAffineMontPoint8
      key.more_odd_multiples odd ⦃ r => r = none ∨ ∃ m, r = some m ∧ P m ⦄
  peek : ∀ key : mid.p384.VerifyingKey, ∃ r, low.generic.reuse_cache.ReuseCache.get_or_build
      (core.default.DefaultArray 8#usize mid.p384.AffineMontPoint.Insts.CoreDefaultDefault)
      mid.p384.VerifyingKey.raw_ecdsa_verify.closure.Insts.CoreOpsFunctionFnOnceTupleArrayAffineMontPoint8
      key.odd_multiples key = ok r
  clone : ∀ c, ∃ c', low.generic.reuse_cache.ReuseCache.Insts.CoreCloneClone.clone
      (Array.Insts.CoreMarkerCopy 8#usize mid.p384.AffineMontPoint.Insts.CoreMarkerCopy)
      (core.default.DefaultArray 8#usize mid.p384.AffineMontPoint.Insts.CoreDefaultDefault) c = ok c'
  point_new : ∃ c, low.generic.reuse_cache.ReuseCache.new
      high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault = ok c
  point_get_or_build_now : ∀ (key : P384SigningKey) (P : high.ecdsa.EncodedPoint → Prop),
    high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint.call_once
      P384C key () ⦃ P ⦄ →
    low.generic.reuse_cache.ReuseCache.get_or_build_now
      high.ecdsa.EncodedPoint.Insts.CoreMarkerCopy high.ecdsa.EncodedPoint.Insts.CoreDefaultDefault
      (high.ecdsa.SigningKey.public_key_uncompressed.closure.Insts.CoreOpsFunctionFnOnceTupleEncodedPoint P384C)
      key.public_key key ⦃ P ⦄

/-- `VerifyingKey::rind_ecdsa_verify`: rind's twin multiplication's ECDSA
verification of `r`, `s`, and `e` under the key's point `Q`. -/
theorem rind_verify_spec (_hr : Runs) (hc : Cached) (key : mid.p384.VerifyingKey)
    (Q : nist.Point) (hQ : p384OnCurve Q) (hQo : P384OrderOf Q) (hpt : p384Represents2 Q (pairNat6 key.point.xy.val))
    (r s e : mid.p384.Scalar) (hr0 : 0 < scNat r) (hr : scNat r < n384) (hs0 : 0 < scNat s)
    (hs : scNat s < n384) (he : scNat e < n384) :
    mid.p384.VerifyingKey.rind_ecdsa_verify key r s e ⦃ res =>
      (ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s) ∧ res = core.result.Result.Ok ()) ∨
        (¬ ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s) ∧
          res = core.result.Result.Err error.Error.BadSignature) ⦄ := by
  unfold mid.p384.VerifyingKey.rind_ecdsa_verify
  have hlt : ∀ x, x % n384 < n384 := fun x => Nat.mod_lt _ n384_pos
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
  have hs' : (scNat s : ZMod n384) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hs0 hs
  have hsinv : (scNat si : ZMod n384) = (scNat s : ZMod n384)⁻¹ := by
    have := congrArg (fun x : Nat => (x : ZMod n384)) hssi
    simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at this
    exact (inv_eq_of_mul_eq_one_right this).symm
  have hR := RInv_mul
  push_cast at hR
  have hu1v : scNat u1 = ((scNat e : ZMod n384) * (scNat s : ZMod n384)⁻¹).val := by
    apply val_of_eq _ _ (by rw [hu1]; exact hlt _)
    simp only [scNat] at *
    rw [hu1, hs3, hsm, hem]
    push_cast [ZMod.natCast_mod]
    rw [hsinv]
    set t : ZMod n384 := (2 ^ 384 : ZMod n384) * (n384RInv : ZMod n384)
    linear_combination (scNat s : ZMod n384)⁻¹ * (scNat e : ZMod n384) * (t + 1) * hR
  have hu2v : scNat u2 = ((scNat r : ZMod n384) * (scNat s : ZMod n384)⁻¹).val := by
    apply val_of_eq _ _ (by rw [hu2]; exact hlt _)
    simp only [scNat] at *
    rw [hu2, hs5, hsm, hrm]
    push_cast [ZMod.natCast_mod]
    rw [hsinv]
    set t : ZMod n384 := (2 ^ 384 : ZMod n384) * (n384RInv : ZMod n384)
    linear_combination (scNat s : ZMod n384)⁻¹ * (scNat r : ZMod n384) * (t + 1) * hR
  have hmore' : ∀ m, more = some m → OddMultiples Q 17 m := by
    intro m hm
    rcases hmore with h | ⟨m', h, hm'⟩
    · rw [h] at hm; cases hm
    · rw [h] at hm; cases hm; exact hm'
  step with twin_multiply_spec _hr u1 u2 Q hQ odd hodd more hmore' as ⟨pt, hpt⟩
  rw [twin384, show ((scNat u1 : Nat) : Int) = Int.ofNat (scNat u1) from rfl, show ((scNat u2 : Nat) : Int) = Int.ofNat (scNat u2) from rfl] at hpt
  simp only [p384ZPow] at hpt
  rw [hu1v, hu2v] at hpt
  unfold ecdsaP384Verifies nist.ecdsaVerifies
  dsimp only [p384Add, p384Pow] at hpt
  rcases hT : nist.add p384 (nist.pow p384 p384G ((scNat e : ZMod n384) * (scNat s : ZMod n384)⁻¹).val)
      (nist.pow p384 Q ((scNat r : ZMod n384) * (scNat s : ZMod n384)⁻¹).val) with _ | ⟨x, y⟩
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

/-- `VerifyingKey::vg_ecdsa_verify`: pyca/verified-garbage's ECDSA
verification of `r`, `s`, and `e` under the key's point `Q`. -/
theorem vg_verify_spec (h : Runs) (vg : low.x86_64.p384_vg.Verify) (key : mid.p384.VerifyingKey)
    (Q : nist.Point) (hQ : p384OnCurve Q) (hpt : p384Represents2 Q (pairNat6 key.point.xy.val))
    (r s e : mid.p384.Scalar) :
    mid.p384.VerifyingKey.vg_ecdsa_verify key vg r s e ⦃ res =>
      (ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s) ∧ res = core.result.Result.Ok ()) ∨
        (¬ ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s) ∧
          res = core.result.Result.Err error.Error.BadSignature) ⦄ := by
  unfold mid.p384.VerifyingKey.vg_ecdsa_verify mid.p384.Scalar.as_bytes
  obtain ⟨hx, hy, hQe⟩ := hpt
  step*
  all_goals try (simp [*, Slice.length, Array.repeat, mid.p384.Scalar.BYTES]; done)
  have hs1l : s1.length = 96 := by simp [Slice.length, s1_post, Array.repeat]
  obtain ⟨hsig, hsigl⟩ := sig_r_post4 sig_r1 sig_s1
    (by simp [sig_r1_post, s2_post, mid.p384.Scalar.BYTES])
    (by simp [sig_s1_post, s3_post, hs1l, mid.p384.Scalar.BYTES])
  have hsgv : (to_slice_mut_back (split_at_mut_back (sig_r1, sig_s1))).val = a.val ++ a1.val := by
    rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by rw [← Slice.length, hsigl, hs1l]; rfl), hsig,
      sig_r1_post, s2_post, sig_s1_post, s3_post, Array.val_to_slice, Array.val_to_slice]
  step with as_bytes_uncompressed_spec h key.point hx hy as ⟨b, hb4, hbc⟩
  step with u64x6_to_be_spec e as ⟨c, hc⟩
  step with vg_p384_verify_spec as ⟨bb, hbb⟩
  have hcb : some (vgNist.coords vgP384.C b.val) = Q := by
    rw [← hQe]; exact congrArg some hbc
  have hdec := vgNist.decode_bv vgP384.curve_matches b.val b.property hb4
  rw [vgBytes, vgBytes, vgBytes, vgNist.hashToInt_len vgP384.curve_matches c.val c.property, hc, hsgv] at hbb
  unfold VG.Spec.Ecdsa.verify at hbb
  rcases hd : VG.Spec.EcKey.decodePublicKey vgP384.C (b.val.map (·.bv)) with _ | Q'
  · rw [hd] at hdec; exact absurd (hcb ▸ hQ) hdec
  rw [hd] at hdec hbb
  obtain ⟨hon, hQ'⟩ := hdec
  have hr : VG.Spec.Weierstrass.ofBytes ((List.map (·.bv) (a.val ++ a1.val)).take vgP384.C.len) = scNat r := by
    rw [List.map_append, List.take_left' (by simp; rfl), vgNist.ofBytes_bv, a_post]
  have hs : VG.Spec.Weierstrass.ofBytes ((List.map (·.bv) (a.val ++ a1.val)).drop vgP384.C.len) = scNat s := by
    rw [List.map_append, List.drop_left' (by simp; rfl), vgNist.ofBytes_bv, a1_post]
  simp only [hr, hs] at hbb
  have hiff := vgNist.verifyWith_iff vgP384.curve_matches (by unfold n384; norm_num) Q' (hQ' ▸ hon)
    (scNat e) (scNat r) (scNat s)
  rw [hQ', hcb] at hiff
  subst hbb
  by_cases hv : ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s)
  · simp [hiff.mpr hv, hv]
  · have : VG.Spec.Ecdsa.verifyWith vgP384.C Q' (scNat e) (scNat r) (scNat s) = false := by
      simpa using mt hiff.mp hv
    simp [this, hv]

/-- The ECDSA verification a key's raw check computes, for `r`, `s`, and
`e` the signature's scalars and the hash's: VG's or rind's, which agree. -/
theorem raw_verify_spec (_hr : Runs) (hvg : RunsP384) (hc : Cached) (key : mid.p384.VerifyingKey)
    (Q : nist.Point) (hQ : p384OnCurve Q) (hQo : P384OrderOf Q) (hpt : p384Represents2 Q (pairNat6 key.point.xy.val))
    (r s e : mid.p384.Scalar) (hr0 : 0 < scNat r) (hr : scNat r < n384) (hs0 : 0 < scNat s)
    (hs : scNat s < n384) (he : scNat e < n384) :
    mid.p384.VerifyingKey.raw_ecdsa_verify key r s e ⦃ res =>
      (ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s) ∧ res = core.result.Result.Ok ()) ∨
        (¬ ecdsaP384Verifies Q (scNat e) (scNat r) (scNat s) ∧
          res = core.result.Result.Err error.Error.BadSignature) ⦄ := by
  unfold mid.p384.VerifyingKey.raw_ecdsa_verify
  obtain ⟨-, t, ht⟩ := hvg
  simp only [ht, bind_ok]
  have hrind := rind_verify_spec _hr hc key Q hQ hQo hpt r s e hr0 hr hs0 hs he
  rcases t with _ | vg
  · exact hrind
  have hvgv := vg_verify_spec _hr vg key Q hQ hpt r s e
  -- x86_64 runs VG's every time; aarch64 first reads whether the multiples
  -- are ready.
  first
    | exact hvgv
    | (obtain ⟨o, ho⟩ := hc.peek key
       simp only [ho, bind_ok]
       split <;> assumption)

/-! ## Verifying keys, `mid::p384::VerifyingKey` -/

/-- An X9.62 key's parse outcome: refused unless an uncompressed point on the
curve, with coordinates below p, and otherwise `good` of what it builds. -/
def x962Outcome {α : Type} (bytes : List U8) (good : α → Prop) (r : core.result.Result α error.Error) :
    Prop :=
  match bytes.head? with
  | none => r = .Err (.KeyRejected .WrongLength)
  | some b0 =>
    if b0 = 4#u8 then
      if bytes.length = 97 then
        if p384OnCurve (some (p384Coords bytes)) then ∃ a, r = .Ok a ∧ good a
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength)
    else r = .Err (.KeyRejected .Compressed)

/-- A verifying key for the point `Q`. -/
def VKey (Q : nist.Point) (key : mid.p384.VerifyingKey) : Prop :=
  p384OnCurve Q ∧ Q ≠ none ∧ p384Represents2 Q (pairNat6 key.point.xy.val)

theorem vk_from_x962_spec (h : Runs) (hheld : Held) (hc : Cached) (bytes : Slice U8) :
    mid.p384.VerifyingKey.from_x962_uncompressed bytes ⦃ r =>
      x962Outcome bytes.val (VKey (some (p384Coords bytes.val))) r ⦄ := by
  unfold mid.p384.VerifyingKey.from_x962_uncompressed
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
    · by_cases hl : bytes.length = 97 <;> simp only [hl, ↓reduceIte] at hr ⊢
      · by_cases hon : p384OnCurve (some (p384Coords bytes.val)) <;> simp only [hon, ↓reduceIte] at hr ⊢
        · obtain ⟨pk, rfl, hpk⟩ := hr
          simp only
          obtain ⟨c, hcv⟩ := hc.new
          rw [hcv]
          simp only [bind_ok, WP.spec_ok]
          exact ⟨_, rfl, hon, by simp, hpk⟩
        · subst hr; simp
      · subst hr; simp
    · subst hr; simp

/-! ## The generic ECDSA layer, `high::ecdsa`, at P-384 -/

theorem from_bytes_reduced_spec (bytes : Slice U8) (hl : bytes.length = 48) :
    mid.p384.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced bytes ⦃ sc =>
      scNat sc = beNat bytes.val % n384 ⦄ := by
  unfold mid.p384.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced mid.p384.Scalar.from_bytes_reduced
  step with be_any_size_48_spec bytes hl as ⟨o, w, ho, hw⟩
  subst ho
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨r, hr⟩
  simp only [core.result.Result.unwrap, WP.spec_ok]
  simp only [scNat] at *
  rw [hr, hw]

/-- Signature verification's outcome under the key `Q`, for the message's
digest `dg`: accepted if `sig` is 96 bytes, its halves big-endian r and s,
that verify over the digest's first 48 bytes, and otherwise refused. -/
def ecdsaVerifyOutcome (Q : nist.Point) (dg sig : List U8) (r : core.result.Result Unit error.Error) : Prop :=
  (sig.length = 96 ∧ ecdsaP384Verifies Q (beNat (dg.take 48) % n384) (beNat (sig.take 48)) (beNat (sig.drop 48)) ∧
    r = .Ok ()) ∨
  (¬ (sig.length = 96 ∧
      ecdsaP384Verifies Q (beNat (dg.take 48) % n384) (beNat (sig.take 48)) (beNat (sig.drop 48))) ∧
    r = .Err .BadSignature)

theorem hash_to_scalar_spec (dg : Slice U8) (hdg : 48 ≤ dg.length) :
    high.ecdsa.hash_to_scalar P384C dg ⦃ r =>
      ∃ e, r = .Ok e ∧ scNat e = beNat (dg.val.take 48) % n384 ⦄ := by
  unfold high.ecdsa.hash_to_scalar
  simp only [mid.p384.Scalar.Insts.RindHighCurveScalar.LEN_BYTES, mid.p384.Scalar.BYTES, 
    bind_ok]
  apply WP.spec_bind (Pₘ := fun h48 : Slice U8 => h48.val = dg.val.take 48)
  · split
    · step as ⟨h48, hh48, _⟩
      simp [hh48, List.slice]
    · rename_i hle
      simp only [WP.spec_ok]
      rw [List.take_of_length_le]
      have : ¬ dg.length > 48 := by simpa [Slice.len] using hle
      simp only [Slice.length] at hdg this ⊢; omega
  intro h48 hh48
  have hl : h48.length = 48 := by
    simp only [Slice.length, hh48, List.length_take]; simp only [Slice.length] at hdg; omega
  step with from_bytes_reduced_spec h48 hl as ⟨e, he⟩
  rw [hh48] at he
  exact ⟨e, rfl, he⟩

theorem ecdsa_verify_spec (h : Runs) (hvg : RunsP384) (hc : Cached) {H Ctx St : Type}
    (hinst : high.hash.SignatureHash H Ctx St)
    (key : high.ecdsa.VerifyingKey high.curve.P384 mid.p384.StaticPrivateKey mid.p384.VerifyingKey mid.p384.Scalar)
    (Q : nist.Point) (hk : VKey Q key.public_key) (hQo : P384OrderOf Q) (msg sig dg : Slice U8)
    (d : high.digest.Digest) (hd : hinst.HashInst.hash msg = ok d)
    (hdg' : high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg) (hdg : 48 ≤ dg.length) :
    high.ecdsa.VerifyingKey.verify P384C hinst key msg sig ⦃ r => ecdsaVerifyOutcome Q dg.val sig.val r ⦄ := by
  unfold high.ecdsa.VerifyingKey.verify
  step
  simp only [mid.p384.Scalar.Insts.RindHighCurveScalar.LEN_BYTES, mid.p384.Scalar.BYTES]
  step as ⟨i2, hi2⟩
  unfold ecdsaVerifyOutcome
  by_cases hlen : sig.length = 96
  · have hne : (sig.len != i2) = false := by
      simp only [bne_eq_false_iff_eq]; apply UScalar.eq_of_val_eq; simp [Slice.len, hi2]
      simpa [Slice.length] using hlen
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hlen, true_and]
    have hsl : sig.val.length = 96 := hlen
    step as ⟨sr, hsr, hsrl⟩
    have hsrv : sr.val = sig.val.take 48 := by rw [hsr]; simp [List.slice]
    unfold mid.p384.Scalar.Insts.RindHighCurveScalar.from_bytes_checked
    step with from_bytes_checked_spec sr hsrl as ⟨rr, hrr⟩
    rw [hsrv] at hrr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      
      high.ecdsa.VerifyingKey.verify.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      
      high.ecdsa.VerifyingKey.verify.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    by_cases hra : 0 < beNat (sig.val.take 48) ∧ beNat (sig.val.take 48) < n384
    · rw [ite_eq_left hra] at hrr
      obtain ⟨scr, rfl, hscr⟩ := hrr
      simp only [bind_ok]
      step as ⟨ss, hss, hssl⟩
      have hssv : ss.val = sig.val.drop 48 := by simp [hss]
      step with from_bytes_checked_spec ss (by rw [hssl]; simp only [Slice.length]; omega) as ⟨rs, hrs⟩
      rw [hssv] at hrs
      by_cases hsa : 0 < beNat (sig.val.drop 48) ∧ beNat (sig.val.drop 48) < n384
      · rw [ite_eq_left hsa] at hrs
        obtain ⟨scs, rfl, hscs⟩ := hrs
        simp only [bind_ok]
        rw [hd]
        simp only [bind_ok]
        rw [hdg']
        simp only [bind_ok]
        step with hash_to_scalar_spec dg hdg as ⟨r4, e, hr4, he⟩
        subst hr4
        simp only [bind_ok, mid.p384.VerifyingKey.Insts.RindHighCurvePublicKeyScalar.raw_ecdsa_verify]
        obtain ⟨hQ, -, hpt⟩ := hk
        apply WP.spec_mono (raw_verify_spec h hvg hc key.public_key Q hQ hQo hpt scr scs e
          (by unfold scNat; rw [hscr]; exact hra.1) (by unfold scNat; rw [hscr]; exact hra.2)
          (by unfold scNat; rw [hscs]; exact hsa.1) (by unfold scNat; rw [hscs]; exact hsa.2)
          (by rw [he]; exact Nat.mod_lt _ n384_pos))
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

/-- `ecdsa::VerifyingKey::from_x962_uncompressed` at P-384. -/
theorem ecdsa_vk_from_x962_spec (h : Runs) (hheld : Held) (hc : Cached) (bytes : Slice U8) :
    high.ecdsa.VerifyingKey.from_x962_uncompressed P384C bytes ⦃ r =>
      x962Outcome bytes.val (fun key => VKey (some (p384Coords bytes.val)) key.public_key) r ⦄ := by
  unfold high.ecdsa.VerifyingKey.from_x962_uncompressed
  step
  simp only [P384C, 
    mid.p384.VerifyingKey.Insts.RindHighCurvePublicKeyScalar,
    mid.p384.VerifyingKey.Insts.RindHighCurvePublicKeyScalar.from_x962_uncompressed]
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

theorem x_scalar_spec (k : mid.p384.StaticPrivateKey) (h : Runs) (hvg : RunsP384) (hk : scNat k.scalar < n384) (x y : Nat)
    (hq : p384Pow p384G (scNat k.scalar) = some (x, y)) (hc : p384OnCurve (some (x, y))) :
    mid.p384.StaticPrivateKey.public_key_x_scalar k ⦃ r => scNat r = x % n384 ⦄ := by
  unfold mid.p384.StaticPrivateKey.public_key_x_scalar mid.p384.AffineMontPoint.x_scalar
  step
  obtain ⟨⟨t, ht⟩, -⟩ := hvg
  simp only [ht, bind_ok]
  rcases t with _ | vg
  swap
  · step with vg_public_key_spec h vg k hk x y hq hc as ⟨b, hb4, hbc⟩
    simp only [mid.p384.FieldElement.BYTES]
    step as ⟨i, hi⟩
    step as ⟨sl, hsl, hsll⟩
    have hbl : b.val.length = 97 := b.property
    have hslv : beNat sl.val = x := by
      have := congrArg Prod.fst hbc
      simp only [p384Coords] at this
      rw [← this, hsl, Array.val_to_slice]
      simp [hi]
    show mid.p384.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced sl ⦃ _ ⦄
    apply WP.spec_mono (from_bytes_reduced_spec sl (by rw [hsll]; simp [hi]))
    intro r hr
    rw [hr, hslv]
  simp only
  step with public_point_spec h k x y hk hq hc as ⟨pt, hpx, hpy, hpx', hpy'⟩
  step with as_bytes_uncompressed_spec h pt hpx hpy as ⟨b, hb4, hbc0⟩
  have hbc : p384Coords b.val = (x, y) := by rw [hbc0, hpx', hpy']
  simp only [mid.p384.FieldElement.BYTES]
  step as ⟨i, hi⟩
  step as ⟨sl, hsl, hsll⟩
  have hbl : b.val.length = 97 := b.property
  have hslv : beNat sl.val = x := by
    have := congrArg Prod.fst hbc
    simp only [p384Coords] at this
    rw [← this, hsl, Array.val_to_slice]
    simp [hi]
  show mid.p384.Scalar.Insts.RindHighCurveScalar.from_bytes_reduced sl ⦃ _ ⦄
  apply WP.spec_mono (from_bytes_reduced_spec sl (by rw [hsll]; simp [hi]))
  intro r hr
  rw [hr, hslv]

@[step]
theorem is_zero_spec (a : mid.p384.Scalar) :
    mid.p384.Scalar.is_zero a ⦃ b => b ↔ scNat a = 0 ⦄ := by
  unfold mid.p384.Scalar.is_zero mid.p384.Scalar.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step as ⟨b, hb⟩
  have : wordsNat (Array.repeat 6#usize core.default.DefaultU64.default).val = 0 := by
    simp [wordsNat, Array.repeat, Nat.ofDigits, core.default.DefaultU64.default]
  rw [hb, this]
  simp [scNat]


/-- A generated key is in [1, n), and generation refuses only with `RngFailed`. -/
def Keygen (res : core.result.Result mid.p384.PrivateKey error.Error) : Prop :=
  (∀ k, res = .Ok k → 0 < wordsNat k.scalar.val ∧ wordsNat k.scalar.val < n384) ∧
    ∀ e, res = .Err e → e = .RngFailed

theorem generate_from_loop_spec {T : Type} (inst : mid.rng.RandomSource T) (hd : Draws inst) (n : Nat)
    (rng : T) : mid.p384.PrivateKey.generate_from_loop inst n rng ⦃ res => Keygen res.1 ⦄ := by
  induction n generalizing rng with
  | zero => simp [mid.p384.PrivateKey.generate_from_loop, Keygen]
  | succ n ih =>
    simp only [mid.p384.PrivateKey.generate_from_loop, Array.to_slice_mut, lift, bind_ok]
    apply WP.spec_bind (hd rng _)
    rintro ⟨r1, rng1, s1⟩ hr1
    rcases r1 with _ | e
    · have hl : ((Array.repeat 48#usize 0#u8).from_slice s1).to_slice.length = 48 := by simp [Slice.length]
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

/-- `p384::StaticPrivateKey::generate`, P-384's `generate_random_key`. -/
theorem static_generate_spec (_h : Runs) {T : Type} (inst : mid.rng.RandomSource T) (hd : Draws inst)
    (rng : T) : mid.p384.StaticPrivateKey.generate inst rng ⦃ res => Keygen res.1 ⦄ := by
  unfold mid.p384.StaticPrivateKey.generate
  exact generate_from_loop_spec inst hd 64 rng

/-- The nonce loop: if it returns a signature, it is (r, s) for some nonce in
[1, n), with neither zero. -/
theorem sign_nonces_spec (h : Runs) (hvg : RunsP384) {T : Type}
    (inst : mid.rng.RandomSource T) (hdr : Draws inst)
    (key : high.ecdsa.SigningKey high.curve.P384 mid.p384.StaticPrivateKey mid.p384.VerifyingKey mid.p384.Scalar)
    (hd : scNat key.private_key.scalar < n384)
    (e : mid.p384.Scalar) (he : scNat e < n384) (rng : T) :
    high.ecdsa.SigningKey.sign_with_nonces_loop P384C inst key e rng ⦃ res =>
      (∀ rs, res.1 = .Ok rs → ∃ k, 0 < k ∧ k < n384 ∧
        ecdsaP384Sign (scNat key.private_key.scalar) k (scNat e) = some (scNat rs.1, scNat rs.2) ∧
        scNat rs.1 ≠ 0 ∧ scNat rs.2 ≠ 0) ∧ ∀ err, res.1 = .Err err → err = .RngFailed ⦄div := by
  unfold high.ecdsa.SigningKey.sign_with_nonces_loop
  revert rng
  dspec_induction loop
  intros loop' ih x
  simp only
  unfold high.ecdsa.SigningKey.sign_with_nonces_loop.body
  simp only [
    
    mid.p384.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.public_key_x_scalar,
    mid.p384.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.raw_ecdsa_sign,
    mid.p384.Scalar.Insts.RindHighCurveScalar.is_zero,
    ]
  step with static_generate_spec h inst hdr x as ⟨res, hres⟩
  obtain ⟨hok, herr⟩ := hres
  obtain ⟨rr, nx⟩ := res
  simp only at hok herr ⊢
  rcases rr with k | err
  · obtain ⟨hk0, hk⟩ := hok k rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨x, y, hq, hc⟩ := p384_g_mult _ hk0 hk
    step with x_scalar_spec k h hvg hk x y hq hc as ⟨r1, hr1⟩
    step as ⟨b, hb⟩
    split
    · rename_i hbt
      simp only [bind_ok]
      exact ih nx
    · rename_i hbf
      have hr0 : scNat r1 ≠ 0 := fun h0 => hbf (hb.mpr h0)
      step with raw_ecdsa_sign_spec key.private_key k e r1 hd hk0 hk he (by rw [hr1]; exact Nat.mod_lt _ n384_pos)
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
        simp only [ecdsaP384Sign, nist.ecdsaSign, hq, hr1, hs1]
  · simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.dspec_ok]
    refine ⟨(fun rs h => nomatch h), fun e2 h => ?_⟩
    simp only [core.convert.FromSame.from, core.result.Result.Err.injEq] at h
    rw [← h]; exact herr err rfl

@[step]
theorem write_bytes_spec (sc : mid.p384.Scalar) (target : Slice U8) (hl : target.length = 48) :
    mid.p384.Scalar.Insts.RindHighCurveScalar.write_bytes sc target ⦃ r =>
      r.length = 48 ∧ beNat r.val = scNat sc ⦄ := by
  unfold mid.p384.Scalar.Insts.RindHighCurveScalar.write_bytes mid.p384.Scalar.as_bytes
  step as ⟨a, ha⟩
  step as ⟨sl, hsl⟩
  step as ⟨r, hr⟩
  refine ⟨by simp [Slice.length, hr, hsl], ?_⟩
  rw [hr, hsl, Array.val_to_slice, ha]

theorem encode_spec (k : mid.p384.StaticPrivateKey) (out : Slice U8) (hl : 48 ≤ out.length) :
    mid.p384.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.encode k out ⦃ r =>
      ∃ sl, r.1 = .Ok sl ⦄ := by
  unfold mid.p384.StaticPrivateKey.Insts.RindHighCurvePrivateKeyScalar.encode
  simp only [core.slice.Slice.get_mut, 
    core.slice.index.SliceIndexRangeUsizeSlice.get_mut]
  rw [ite_eq_left (by simp; omega)]
  simp only [bind_ok, mid.p384.StaticPrivateKey.secret_bytes, mid.p384.PrivateKey.secret_bytes,
    mid.p384.Scalar.as_bytes]
  step*


/-- An ECDSA signature's outcome, for private key `d` and the hash's integer
`e`: 96 bytes at the start of the output, the big-endian r and s of some
nonce in [1, n), neither zero; refused if the output is short, a nonce draw
fails, or none of a nonce's 64 draws is in [1, n). -/
def ecdsaSignOutcome (d e : Nat) (outLen : Nat)
    (r : core.result.Result (Slice U8) error.Error × Slice U8) : Prop :=
  (∀ out, r.1 = .Ok out → out.length = 96 ∧ r.2.length = outLen ∧ r.2.val.take 96 = out.val ∧
    ∃ k, 0 < k ∧ k < n384 ∧
    ecdsaP384Sign d k e = some (beNat (out.val.take 48), beNat (out.val.drop 48)) ∧
    beNat (out.val.take 48) ≠ 0 ∧ beNat (out.val.drop 48) ≠ 0) ∧
  ∀ err, r.1 = .Err err → (outLen < 96 ∧ err = .WrongLength) ∨ err = .RngFailed

theorem p384c_len : P384C.ScalarInst.LEN_BYTES = ok 48#usize := by
  simp only [
    mid.p384.Scalar.Insts.RindHighCurveScalar.LEN_BYTES,
    mid.p384.Scalar.BYTES]

theorem get_mut_rangeTo (s : Slice U8) (r : core.ops.range.RangeTo Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexRangeToUsizeSlice U8) s r =
      core.slice.index.SliceIndexRangeToUsizeSlice.get_mut r s := rfl

theorem rfc6979_spec (h : Runs) (hvg : RunsP384) (hdrbg : Drbg) {H Ctx St : Type}
    (hinst : high.hash.Hash H Ctx St)
    (key : high.ecdsa.SigningKey high.curve.P384 mid.p384.StaticPrivateKey mid.p384.VerifyingKey mid.p384.Scalar)
    (hd : scNat key.private_key.scalar < n384)
    (msg random sig dg : Slice U8) (d : high.digest.Digest) (hhash : hinst.hash msg = ok d)
    (hdg' : high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg) (hdg : 48 ≤ dg.length) :
    high.ecdsa.SigningKey.rfc6979_sign_with_random P384C hinst key msg random sig ⦃ r =>
      ecdsaSignOutcome (scNat key.private_key.scalar) (beNat (dg.val.take 48) % n384) sig.length r ⦄div := by
  unfold high.ecdsa.SigningKey.rfc6979_sign_with_random
  rw [p384c_len]
  simp only [bind_ok]
  step as ⟨i1, hi1⟩
  rw [get_mut_rangeTo]
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  have hsl' : sig.val.length = sig.length := rfl
  by_cases hlen : 96 ≤ sig.length
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
  apply WP.dspec_bind (sign_nonces_spec h hvg _ (hdrbg.draws_spec hinst) key hd e (by rw [he]; exact Nat.mod_lt _ n384_pos) g)
  rintro ⟨r2, g2⟩ ⟨hr2ok, hr2err⟩
  simp only at hr2ok hr2err
  simp only [uncurry]
  rcases r2 with ⟨rr, ss⟩ | err
  · obtain ⟨k, hk0, hk, hsign, hr0, hs0⟩ := hr2ok _ rfl
    simp only [bind_ok]
    step as ⟨s6, back6, hs6, hs6l, hback6⟩
    step with write_bytes_spec rr s6 (by rw [hs6l]) as ⟨s7, hs7l, hs7⟩
    set O := List.slice 0 i1.val sig.val with hOdef
    have hOl : O.length = 96 := by simp [hOdef, List.slice, hi1]; omega
    have h6 : (back6 s7).val = s7.val ++ O.drop 48 := by
      rw [hback6, Slice.from_val]
      have := setSlice!_append [] (O.take 48) (O.drop 48) s7.val (by simp [Slice.length] at hs7l; simp [hs7l, hOl])
      simp only [List.nil_append, List.take_append_drop, List.length_nil] at this
      rw [← this]
    have hs7l' : s7.val.length = 48 := hs7l
    have hb6l : (back6 s7).val.length = 96 := by simp [h6, hs7l', hOl]
    step as ⟨s8, back8, hs8, hs8l, hback8⟩
    have hs8v : s8.length = 48 := by rw [hs8l]; simp only [Slice.length, hb6l]
    step with write_bytes_spec ss s8 hs8v as ⟨s9, hs9l, hs9⟩
    have h8 : (back8 s9).val = s7.val ++ s9.val := by
      rw [hback8, h6]
      have := setSlice!_append s7.val (O.drop 48) [] s9.val (by simp [Slice.length] at hs9l; simp [hs9l, hOl])
      simp only [List.append_nil, hs7l'] at this
      exact this
    step as ⟨i2, hi2⟩
    step as ⟨s10, hs10, hs10l⟩
    simp only [WP.dspec_ok, ecdsaSignOutcome]
    have hs9l' : s9.val.length = 48 := hs9l
    have hv : s10.val = s7.val ++ s9.val := by
      rw [hs10, h8, hi2]; simp [List.slice, hs7l', hs9l']
    refine ⟨fun out hout => ?_, fun err h => nomatch h⟩
    cases hout
    have hb8 : (back8 s9).val.length = 96 := by simp [h8, hs7l', hs9l']
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


/-- `ecdsa::SigningKey::sign` at P-384. -/
theorem ecdsa_sign_spec (h : Runs) (hvg : RunsP384) (hdrbg : Drbg) (hfill : Fills)
    {H Ctx St : Type} (hinst : high.hash.SignatureHash H Ctx St)
    (key : high.ecdsa.SigningKey high.curve.P384 mid.p384.StaticPrivateKey mid.p384.VerifyingKey mid.p384.Scalar)
    (hd : scNat key.private_key.scalar < n384)
    (msg sig dg : Slice U8) (d : high.digest.Digest) (hhash : hinst.HashInst.hash msg = ok d)
    (hdg' : high.digest.Digest.Insts.CoreConvertAsRefSliceU8.as_ref d = ok dg) (hdg : 48 ≤ dg.length) :
    high.ecdsa.SigningKey.sign P384C hinst key msg sig ⦃ r =>
      ecdsaSignOutcome (scNat key.private_key.scalar) (beNat (dg.val.take 48) % n384) sig.length r ⦄div := by
  unfold high.ecdsa.SigningKey.sign mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill
  step
  step as ⟨rs, back, hrs, hback⟩
  obtain ⟨⟨fr, fs⟩, hf⟩ := hfill rs
  rw [hf]
  simp only [bind_ok, uncurry]
  rcases fr with _ | ferr
  · simp only [core.result.Result.map_err, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨rnd, hrnd⟩
    exact rfc6979_spec h hvg hdrbg hinst.HashInst key hd msg rnd sig dg d hhash hdg' hdg
  · simp only [core.result.Result.map_err, bind_tc_ok, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      
      mid.rng.RandomSourceSystemRandom.fill.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ecdsaSignOutcome]
    simp

end P384

end rind.x86_64
