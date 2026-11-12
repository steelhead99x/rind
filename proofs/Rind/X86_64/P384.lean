import Rind.X86_64.S2nBignum
import Rind.X86_64.Dispatch
import Rind.Bytes
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result rind.spec

/-!
# P-384 ECDH, proven from rind's agreement to s2n-bignum's contracts

`p384_agree` states what the agreement API returns for `ECDH_P384`, in terms
of `p384Pow`, HOL Light's `group_pow p384_group`, through the dispatch
`Rind.X86_64.Dispatch` models. rind keeps points in Montgomery form,
which `mont_on_curve` relates to the curve equation, and runs s2n-bignum's
`p384_montjscalarmul` on Jacobian coordinates, which `as_affine_spec`
converts back. `admin/prove` writes the aarch64 proof from this file by
renaming the target.
-/

set_option exponentiation.threshold 400

namespace rind.x86_64

/-! ## What the theorems state -/

/-- The coordinates an encoded P-384 point names, read big-endian after its
tag byte. -/
def p384Coords (bytes : List U8) : Nat × Nat :=
  (beNat (bytes.slice 1 49), beNat (bytes.slice 49 97))

/-- P-384 ECDH's outcome, for scalar `k` and the peer's encoded key: refused
unless it is an X9.62 uncompressed point on the curve, with coordinates below
`p384`, and otherwise the x-coordinate of `k` times that point, or a fault
unless that is a finite point on the curve. -/
def p384Agreement (k : Nat) (peer : List U8) (r : core.result.Result high.agreement.Secret error.Error) :
    Prop :=
  match peer.head? with
  | none => r = .Err (.KeyRejected .WrongLength)
  | some b0 =>
    if b0 = 4#u8 then
      if peer.length = 97 then
        if p384OnCurve (some (p384Coords peer)) then
          match p384Pow (some (p384Coords peer)) k with
          | some (x, y) =>
            if p384OnCurve (some (x, y)) then ∃ s, r = .Ok (.P384 s) ∧ beNat s.val = x
            else r = .Err .Fault
          | none => r = .Err .Fault
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength)
    else r = .Err (.KeyRejected .Compressed)

/-! The P-384 lemmas' own namespace keeps their names apart from other curves'. -/
namespace P384

/-! ## Byte and limb conversions, `mid::util` -/

theorem be_to_u64x6_loop_spec (b : Std.Array U8 48#usize) (iter : core.ops.range.Range Std.Usize)
    (r : Std.Array U64 6#usize)
    (hs : iter.start.val ≤ 6) (he : iter.end.val = 6)
    (hr : ∀ i < iter.start.val, (r.val[i]!).val = beNat (b.val.slice (8 * (5 - i)) (8 * (6 - i)))) :
    mid.util.big_endian_to_u64x6_loop iter b r ⦃ r' =>
      ∀ i < 6, (r'.val[i]!).val = beNat (b.val.slice (8 * (5 - i)) (8 * (6 - i))) ⦄ := by
  unfold mid.util.big_endian_to_u64x6_loop
  apply loop.spec_decr_nat (fun x => 6 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 6 ∧
      ∀ i < x.1.start.val, (x.2.val[i]!).val = beNat (b.val.slice (8 * (5 - i)) (8 * (6 - i))))
  · rintro ⟨it, r⟩ ⟨hs, he, hr⟩
    simp only at hs he hr ⊢
    unfold mid.util.big_endian_to_u64x6_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step*
      · rcases r1 with a | _
        · exact ⟨a, rfl⟩
        · exact absurd (by rw [b1_post1, i4_post, i2_post, i3_post, i1_post, i_post]; omega) r1_post
      · subst r1_post
        obtain ⟨hab, -⟩ := r1_post
        have hi : i5.val = beNat (b.val.slice (8 * (5 - it.start.val)) (8 * (6 - it.start.val))) := by
          rw [val_of_fromBEBytes _ i5 i5_post, hab, b1_post, i2_post, i1_post, i_post, i4_post,
            i3_post, Array.val_to_slice]
          congr 2 <;> omega
        refine ⟨by omega, by simp [he1, he], ?_, by omega⟩
        intro j hj
        rw [a1_post, Std.Array.set_val_eq]
        by_cases hjs : j = it.start.val
        · subst hjs
          simp_lists [hi]
        · have h := hr j (by omega)
          simp_lists at h ⊢
          exact h
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      intro i hi
      exact hr i (by omega)
  · exact ⟨hs, he, hr⟩

@[step]
theorem be_to_u64x6_spec (b : Std.Array U8 48#usize) :
    mid.util.big_endian_to_u64x6 b ⦃ w => wordsNat w.val = beNat b.val ⦄ := by
  unfold mid.util.big_endian_to_u64x6
  apply WP.spec_mono (be_to_u64x6_loop_spec b _ _ (by simp) (by simp) (by simp))
  intro w hw
  rw [wordsNat_six _ w.property, beNat_48 _ b.property, hw 0 (by omega), hw 1 (by omega),
    hw 2 (by omega), hw 3 (by omega), hw 4 (by omega), hw 5 (by omega)]

/-- The bytes `u64::to_be_bytes` writes. -/
def beBytes (w : U64) : List U8 := w.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)

theorem length_beBytes (w : U64) : (beBytes w).length = 8 := by
  simp [beBytes]

theorem u64x6_to_be_loop_spec (v : Std.Array U64 6#usize) (iter : core.ops.range.Range Std.Usize)
    (r : Std.Array U8 48#usize)
    (hs : iter.start.val ≤ 6) (he : iter.end.val = 6)
    (hr : r.val = List.replicate (8 * (6 - iter.start.val)) 0#u8 ++
      ((v.val.take iter.start.val).reverse.flatMap beBytes)) :
    mid.util.u64x6_to_big_endian_loop iter v r ⦃ r' =>
      r'.val = v.val.reverse.flatMap beBytes ⦄ := by
  unfold mid.util.u64x6_to_big_endian_loop
  apply loop.spec_decr_nat (fun x => 6 - x.1.start.val)
    (fun x => x.1.start.val ≤ 6 ∧ x.1.end.val = 6 ∧
      x.2.val = List.replicate (8 * (6 - x.1.start.val)) 0#u8 ++
        ((v.val.take x.1.start.val).reverse.flatMap beBytes))
  · rintro ⟨it, r⟩ ⟨hs, he, hr⟩
    simp only at hs he hr ⊢
    unfold mid.util.u64x6_to_big_endian_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have hv : (v.val).length = 6 := v.property
      step*
      · rw [s_post1, s1_post]
        simp [i4_post, i3_post, i2_post, i1_post, i_post]
        omega
      · refine ⟨by omega, by simp [he1, he], ?_, by omega⟩
        have hs1 : s1.val = beBytes (v.val[it.start.val]) := by
          rw [s1_post, Array.val_to_slice, a_post, i5_post, beBytes]
        rw [s_post2, s2_post, hs1, hr, show 8 * (6 - it.start.val) = 8 * (5 - it.start.val) + 8 by omega,
          ← List.replicate_append_replicate, show i2.val = (List.replicate (8 * (5 - it.start.val)) 0#u8).length by
            simp [i2_post, i1_post, i_post]; omega,
          setSlice!_append _ _ _ _ (by simp [length_beBytes]), hst,
          show 8 * (6 - (it.start.val + 1)) = 8 * (5 - it.start.val) by omega]
        simp only [List.append_assoc, List.append_cancel_left_eq]
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.reverse_append, List.flatMap_append]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have h6 : it.start.val = 6 := by omega
      have hv : (v.val).length = 6 := v.property
      rw [hr, h6, List.take_of_length_le (by omega)]
      simp
  · exact ⟨hs, he, hr⟩

theorem beNat_beBytes (w : U64) : beNat (beBytes w) = w.val := beNat_toBEBytes w

@[step]
theorem u64x6_to_be_spec (v : Std.Array U64 6#usize) :
    mid.util.u64x6_to_big_endian v ⦃ b => beNat b.val = wordsNat v.val ⦄ := by
  unfold mid.util.u64x6_to_big_endian
  apply WP.spec_mono (u64x6_to_be_loop_spec v _ _ (by simp) (by simp) (by simp))
  intro b hb
  rw [hb]
  have hv : (v.val).length = 6 := v.property
  generalize v.val = l at hv ⊢
  match l, hv with
  | [a, b, c, d, e, f], _ =>
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, beNat_append, length_beBytes,
      beNat_beBytes, wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil,
      List.length_append]
    ring

@[step]
theorem be_slice_to_u64x6_spec (s : Slice U8) :
    mid.util.big_endian_slice_to_u64x6 s ⦃ o =>
      if s.length = 48 then ∃ w, o = some w ∧ wordsNat w.val = beNat s.val else o = none ⦄ := by
  unfold mid.util.big_endian_slice_to_u64x6
  step*
  rcases r with a | _
  · obtain ⟨ha, hl⟩ := r_post
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    step*
  · simp [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, r_post]

/-! ## Field elements and points, `mid::p384` -/

/-- The number a field element's limbs encode. -/
abbrev feNat (fe : mid.p384.FieldElement) : Nat := wordsNat fe.val

theorem p384_pos : 0 < p384 := by simp [p384]

theorem p384_lt : p384 < 2 ^ 384 := by simp only [p384]; decide

@[step]
theorem as_mont_spec (_h : Runs) (fe : mid.p384.FieldElement) :
    mid.p384.FieldElement.as_mont fe ⦃ r => feNat r = 2 ^ 384 * feNat fe % p384 ⦄ := by
  unfold mid.p384.FieldElement.as_mont mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem demont_spec (_h : Runs) (fe : mid.p384.FieldElement) (hfe : feNat fe < p384) :
    mid.p384.FieldElement.demont fe ⦃ r => feNat r = p384RInv * feNat fe % p384 ⦄ := by
  unfold mid.p384.FieldElement.demont mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem inv_spec (fe : mid.p384.FieldElement) :
    mid.p384.FieldElement.inv fe ⦃ r =>
      feNat r < p384 ∧ (feNat fe % p384 = 0 → feNat r = 0) ∧
        (feNat fe % p384 ≠ 0 → feNat fe * feNat r % p384 = 1) ⦄ := by
  unfold mid.p384.FieldElement.inv mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem fe_add_spec (a b : mid.p384.FieldElement) (ha : feNat a < p384) (hb : feNat b < p384) :
    mid.p384.FieldElement.add a b ⦃ r => feNat r = (feNat a + feNat b) % p384 ⦄ := by
  unfold mid.p384.FieldElement.add mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem mont_mul_spec (_h : Runs) (a b : mid.p384.FieldElement) (ha : feNat a < p384)
    (hb : feNat b < p384) :
    mid.p384.FieldElement.mont_mul a b ⦃ r => feNat r = p384RInv * feNat a * feNat b % p384 ⦄ := by
  unfold mid.p384.FieldElement.mont_mul mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  exact a_post (le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb)
    (Nat.mul_le_mul_right _ (le_of_lt p384_lt))))

@[step]
theorem mont_sqr_spec (_h : Runs) (a : mid.p384.FieldElement) (ha : feNat a < p384) :
    mid.p384.FieldElement.mont_sqr a ⦃ r => feNat r = p384RInv * feNat a ^ 2 % p384 ⦄ := by
  unfold mid.p384.FieldElement.mont_sqr mid.p384.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  exact a_post (by
    rw [pow_two]
    exact le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' ha ha)
      (Nat.mul_le_mul_right _ (le_of_lt p384_lt))))

theorem pairNat6_drop (l : List U64) (h : l.length = 12) : (pairNat6 l).2 = wordsNat (l.drop 6) := by
  simp [pairNat6, List.take_of_length_le, h]

theorem pairNat6_append (a b : List U64) (ha : a.length = 6) (hb : b.length = 6) :
    pairNat6 (a ++ b) = (wordsNat a, wordsNat b) := by
  simp [pairNat6, ha, List.take_of_length_le, hb]

@[step]
theorem point_x_spec (pt : mid.p384.AffineMontPoint) :
    mid.p384.AffineMontPoint.x pt ⦃ fe => feNat fe = (pairNat6 pt.xy.val).1 ⦄ := by
  unfold mid.p384.AffineMontPoint.x
  have hl : (pt.xy.val).length = 12 := pt.xy.property
  step*
  · simp [mid.p384.AffineMontPoint.X]
  · simp [mid.p384.AffineMontPoint.X]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p384.AffineMontPoint.X]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [feNat, ha, s_post, mid.p384.AffineMontPoint.X, List.slice, pairNat6]

@[step]
theorem point_y_spec (pt : mid.p384.AffineMontPoint) :
    mid.p384.AffineMontPoint.y pt ⦃ fe => feNat fe = (pairNat6 pt.xy.val).2 ⦄ := by
  unfold mid.p384.AffineMontPoint.y
  have hl : (pt.xy.val).length = 12 := pt.xy.property
  rw [pairNat6_drop _ hl]
  step*
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [mid.p384.AffineMontPoint.Y]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p384.AffineMontPoint.Y]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [feNat, ha, s_post, mid.p384.AffineMontPoint.Y, List.slice, List.take_of_length_le, hl]

@[step]
theorem from_xy_spec (x y : mid.p384.FieldElement) :
    mid.p384.AffineMontPoint.from_xy x y ⦃ pt => pairNat6 pt.xy.val = (feNat x, feNat y) ⦄ := by
  unfold mid.p384.AffineMontPoint.from_xy mid.p384.AffineMontPoint.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index]
  step*
  · simp [mid.p384.AffineMontPoint.X]
  · simp [mid.p384.AffineMontPoint.X]
  · simp [s_post1, mid.p384.AffineMontPoint.X]
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [mid.p384.AffineMontPoint.Y]
  · simp [s3_post1, mid.p384.AffineMontPoint.Y]
  · have hx : (x.val).length = 6 := x.property
    have hy : (y.val).length = 6 := y.property
    rw [s3_post2, s5_post, s2_post, s_post2]
    have h12 : (Array.repeat 12#usize core.default.DefaultU64.default).val =
        [] ++ List.replicate 6 core.default.DefaultU64.default ++
          List.replicate 6 core.default.DefaultU64.default := by
      simp [Array.repeat]
    simp only [mid.p384.AffineMontPoint.X, mid.p384.AffineMontPoint.Y, Array.val_to_slice, h12]
    rw [show (0#usize).val = ([] : List U64).length by simp,
      setSlice!_append _ _ _ _ (by simp [hx]), List.nil_append,
      show (6#usize).val = x.val.length by simp [hx],
      ← List.append_nil (x.val ++ List.replicate 6 _), setSlice!_append _ _ _ _ (by simp [hy])]
    simp [pairNat6_append _ _ hx hy]

theorem CURVE_A_MONT_val : feNat mid.p384.CURVE_A_MONT = 2 ^ 384 * (p384 - 3) % p384 := by
  simp only [feNat, mid.p384.CURVE_A_MONT, Array.make, Array.from_val, wordsNat, p384]
  decide

theorem CURVE_B_MONT_val : feNat mid.p384.CURVE_B_MONT = 2 ^ 384 * b384 % p384 := by
  simp only [feNat, mid.p384.CURVE_B_MONT, Array.make, Array.from_val, wordsNat, p384, b384]
  decide

theorem CURVE_ONE_MONT_val : feNat mid.p384.CURVE_ONE_MONT = 2 ^ 384 % p384 := by
  simp only [feNat, mid.p384.CURVE_ONE_MONT, Array.make, Array.from_val, wordsNat, p384]
  decide

theorem rinv_cast : ((2 ^ 384 : Nat) : ZMod p384) * (p384RInv : ZMod p384) = 1 := by
  have := congrArg (fun n : Nat => (n : ZMod p384)) p384RInv_spec.2
  simpa only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] using this

/-- rind's curve check, in Montgomery form, is the curve equation on the
coordinates it encodes. -/
theorem mont_on_curve (X Y : Nat) :
    p384RInv * Y ^ 2 % p384 =
        (p384RInv * ((p384RInv * X ^ 2 % p384 + 2 ^ 384 * (p384 - 3) % p384) % p384) * X % p384 +
          2 ^ 384 * b384 % p384) % p384 ↔
      p384OnCurve (some (p384RInv * X % p384, p384RInv * Y % p384)) := by
  have hRr := rinv_cast
  generalize (2 : Nat) ^ 384 = R at hRr ⊢
  simp only [p384OnCurve, nist.OnCurve, Nat.mod_lt _ p384_pos, true_and]
  rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff']
  push_cast [ZMod.natCast_mod]
  constructor
  · intro h
    linear_combination (p384RInv : ZMod p384) * h +
      (((p384 - 3 : Nat) : ZMod p384) * p384RInv * X + b384) * hRr
  · intro g
    linear_combination (R : ZMod p384) * g -
      ((p384RInv : ZMod p384) * Y ^ 2 - (p384RInv : ZMod p384) ^ 2 * X ^ 3) * hRr

theorem fe_lt_p384 (fe : mid.p384.FieldElement) (n : Nat) (h : feNat fe = n % p384) : feNat fe < p384 := by
  rw [h]; exact Nat.mod_lt _ p384_pos

@[step]
theorem on_curve_spec (_h : Runs) (pt : mid.p384.AffineMontPoint) (hx : (pairNat6 pt.xy.val).1 < p384)
    (hy : (pairNat6 pt.xy.val).2 < p384) :
    mid.p384.AffineMontPoint.on_curve pt ⦃ b =>
      (b ↔ p384OnCurve (some (p384RInv * (pairNat6 pt.xy.val).1 % p384,
        p384RInv * (pairNat6 pt.xy.val).2 % p384))) ⦄ := by
  unfold mid.p384.AffineMontPoint.on_curve
  step as ⟨x, hxv⟩
  have hx' : feNat x < p384 := by rw [hxv]; exact hx
  step as ⟨r0, hr0⟩
  have hA : feNat mid.p384.CURVE_A_MONT < p384 := by
    rw [CURVE_A_MONT_val]; exact Nat.mod_lt _ p384_pos
  have hr0' := fe_lt_p384 _ _ hr0
  step as ⟨r1, hr1⟩
  have hr1' := fe_lt_p384 _ _ hr1
  step as ⟨r2, hr2⟩
  have hr2' := fe_lt_p384 _ _ hr2
  have hB : feNat mid.p384.CURVE_B_MONT < p384 := by
    rw [CURVE_B_MONT_val]; exact Nat.mod_lt _ p384_pos
  step as ⟨r3, hr3⟩
  step as ⟨y, hyv⟩
  have hy' : feNat y < p384 := by rw [hyv]; exact hy
  step as ⟨l, hl'⟩
  step*
  rw [b_post, s_post, s1_post, Array.val_to_slice, Array.val_to_slice, decide_eq_true_iff,
    ← mont_on_curve, ← hxv, ← hyv, ← CURVE_A_MONT_val, ← CURVE_B_MONT_val]
  simp only [feNat] at hl' hr3 hr2 hr1 hr0
  rw [hl', hr3, hr2, hr1, hr0]

theorem rinv_tomont (x : Nat) (hx : x < p384) : p384RInv * (2 ^ 384 * x % p384) % p384 = x := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod,
    Nat.mul_comm p384RInv, p384RInv_spec.2, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hx]

/-- The limbs of `CURVE_PRIME`, most significant last. -/
theorem CURVE_PRIME_val : mid.p384.CURVE_PRIME.val =
    [4294967295#u64, 18446744069414584320#u64, 18446744073709551614#u64,
      18446744073709551615#u64, 18446744073709551615#u64, 18446744073709551615#u64] := by
  simp [mid.p384.CURVE_PRIME, Array.make]

/-- Comparing limbs from the top, the first that differ decide which number
is smaller. -/
theorem lt_p384_of_top (v : List U64) (hv : v.length = 6) (s : Nat) (hs : s < 6)
    (heq : ∀ k < s, v[5 - k]! = mid.p384.CURVE_PRIME.val[5 - k]!)
    (hne : v[5 - s]! ≠ mid.p384.CURVE_PRIME.val[5 - s]!) :
    wordsNat v < p384 ↔ v[5 - s]!.val < (mid.p384.CURVE_PRIME.val[5 - s]!).val := by
  match v, hv with
  | [a, b, c, d, e, f], _ =>
    have ha := a.hBounds
    have hb := b.hBounds
    have hc := c.hBounds
    have hd := d.hBounds
    have he := e.hBounds
    have hf := f.hBounds
    simp only [UScalarTy.numBits] at ha hb hc hd he hf
    simp only [CURVE_PRIME_val, UScalar.eq_equiv] at heq hne ⊢
    simp only [wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil, p384]
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hne ⊢; omega
    · have e5 := heq 0 (by omega)
      simp at hne e5 ⊢; omega
    · have e5 := heq 0 (by omega)
      have e4 := heq 1 (by omega)
      simp at hne e5 e4 ⊢; omega
    · have e5 := heq 0 (by omega)
      have e4 := heq 1 (by omega)
      have e3 := heq 2 (by omega)
      simp at hne e5 e4 e3 ⊢; omega
    · have e5 := heq 0 (by omega)
      have e4 := heq 1 (by omega)
      have e3 := heq 2 (by omega)
      have e2 := heq 3 (by omega)
      simp at hne e5 e4 e3 e2 ⊢; omega
    · have e5 := heq 0 (by omega)
      have e4 := heq 1 (by omega)
      have e3 := heq 2 (by omega)
      have e2 := heq 3 (by omega)
      have e1 := heq 4 (by omega)
      simp at hne e5 e4 e3 e2 e1 ⊢; omega

theorem getElem_eq_getElem! {α : Type _} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i] = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wordsNat_CURVE_PRIME : wordsNat mid.p384.CURVE_PRIME.val = p384 := by
  simp only [CURVE_PRIME_val, wordsNat, p384]; decide

theorem below_p_loop_spec (v : Std.Array U64 6#usize) (iter : core.ops.range.Range Std.Usize)
    (hs : iter.start.val ≤ 6) (he : iter.end.val = 6)
    (heq : ∀ k < iter.start.val, v.val[5 - k]! = mid.p384.CURVE_PRIME.val[5 - k]!) :
    mid.p384.public_below_p_loop
      iter v ⦃ b => (b ↔ wordsNat v.val < p384) ⦄ := by
  have hv : (v.val).length = 6 := v.property
  unfold mid.p384.public_below_p_loop
  apply loop.spec_decr_nat (fun x => 6 - x.start.val)
    (fun x => x.start.val ≤ 6 ∧ x.end.val = 6 ∧
      ∀ k < x.start.val, v.val[5 - k]! = mid.p384.CURVE_PRIME.val[5 - k]!)
  · rintro it ⟨hs, he, heq⟩
    unfold mid.p384.public_below_p_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step*
      · rename_i hne
        have hj : j.val < 6 := by omega
        have hne' : v.val[5 - it.start.val]! ≠ mid.p384.CURVE_PRIME.val[5 - it.start.val]! := by
          rw [← j_post, ← getElem_eq_getElem! _ _ (by omega),
            ← getElem_eq_getElem! _ _ (by simp [CURVE_PRIME_val]; omega), ← i1_post, ← i2_post]
          simpa using hne
        rw [lt_p384_of_top v.val hv _ (by omega) heq hne', decide_eq_true_iff, UScalar.lt_equiv,
          i1_post, i2_post, ← j_post, getElem_eq_getElem! _ _ (by omega),
          getElem_eq_getElem! _ _ (by simp [CURVE_PRIME_val]; omega)]
      · rename_i heq1
        refine ⟨by omega, by simp [he1, he], ?_, by omega⟩
        intro k hk
        by_cases hks : k = it.start.val
        · subst hks
          rw [← j_post, ← getElem_eq_getElem! _ _ (by omega),
            ← getElem_eq_getElem! _ _ (by simp [CURVE_PRIME_val]; omega), ← i1_post, ← i2_post]
          exact UScalar.eq_of_val_eq (by simpa using heq1)
        · exact heq k (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_lt]
      have hall : v.val = mid.p384.CURVE_PRIME.val := by
        apply List.ext_getElem! (by simp [hv, CURVE_PRIME_val])
        intro n
        by_cases hn : n < 6
        · have := heq (5 - n) (by omega)
          rwa [show 5 - (5 - n) = n by omega] at this
        · simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega : v.val.length ≤ n),
            List.getElem?_eq_none (by simp [CURVE_PRIME_val]; omega :
              mid.p384.CURVE_PRIME.val.length ≤ n)]
      rw [hall, wordsNat_CURVE_PRIME]
  · exact ⟨hs, he, heq⟩

@[step]
theorem below_p_spec (v : Std.Array U64 6#usize) :
    mid.p384.public_below_p v ⦃ b => (b ↔ wordsNat v.val < p384) ⦄ :=
  below_p_loop_spec v _ (by simp) (by simp) (by simp)

theorem from_x962_spec (_h : Runs) (bytes : Slice U8) :
    mid.p384.AffineMontPoint.from_x962_uncompressed bytes ⦃ r =>
      match bytes.val.head? with
      | none => r = .Err (.KeyRejected .WrongLength)
      | some b0 =>
        if b0 = 4#u8 then
          if bytes.length = 97 then
            if p384OnCurve (some (p384Coords bytes.val)) then
              ∃ pt, r = .Ok pt ∧ p384Represents2 (some (p384Coords bytes.val)) (pairNat6 pt.xy.val)
            else r = .Err (.KeyRejected .NotOnCurve)
          else r = .Err (.KeyRejected .WrongLength)
        else r = .Err (.KeyRejected .Compressed) ⦄ := by
  unfold mid.p384.AffineMontPoint.from_x962_uncompressed
  simp only [core.slice.Slice.first, core.convert.IntoFrom.into,
    error.Error.Insts.CoreConvertFromKeyFormatError.from]
  rcases hb : bytes.val.head? with _ | b0
  · simp
  · simp only [bind_ok]
    split
    · have h4 : (4#8#uscalar : U8) = 4#u8 := UScalar.eq_of_val_eq rfl
      simp only [h4, ↓reduceIte]
      simp only [mid.p384.PublicKey.BYTES, mid.p384.FieldElement.BYTES]
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      by_cases hl : bytes.length = 97
      · have hlen : (bytes.len != i2) = false := by
          simp only [bne_eq_false_iff_eq]
          apply UScalar.eq_of_val_eq
          simp [Slice.len, hi2, hi1]; simpa [Slice.length] using hl
        simp only [hlen, Bool.false_eq_true, ↓reduceIte, hl]
        step as ⟨_, xy, _, _, _, hxy⟩
        step as ⟨x, y, hxl, _, hx, hy⟩
        have hyl : y.length = 48 := by
          simp only [Slice.length, hy, hxy, List.length_drop]; simp [Slice.length] at hl; omega
        step as ⟨o1, ho1⟩
        simp only [hxl, ↓reduceIte] at ho1
        obtain ⟨x1, rfl, hx1⟩ := ho1
        step as ⟨x1', hx1'⟩
        cases hx1'
        step as ⟨o2, ho2⟩
        simp only [hyl, ↓reduceIte] at ho2
        obtain ⟨y1, rfl, hy1⟩ := ho2
        step as ⟨y1', hy1'⟩
        cases hy1'
        have hc : p384Coords bytes.val = (wordsNat x1.val, wordsNat y1.val) := by
          rw [hx1, hy1, hx, hy, hxy, p384Coords]
          simp only [List.slice, List.drop_drop]
          simp [Slice.length] at hl
          congr 2
          rw [List.take_of_length_le (by simp; omega)]
        rw [hc]
        step as ⟨bx, hbx⟩
        by_cases hxp : wordsNat x1.val < p384
        · simp only [hxp, iff_true] at hbx
          simp only [hbx, ↓reduceIte]
          step as ⟨by', hby⟩
          by_cases hyp : wordsNat y1.val < p384
          · simp only [hyp, iff_true] at hby
            simp only [hby, ↓reduceIte]
            step as ⟨fx, hfx⟩
            step as ⟨fy, hfy⟩
            step as ⟨pt, hpt⟩
            have hfxp : feNat fx < p384 := fe_lt_p384 _ _ hfx
            have hfyp : feNat fy < p384 := fe_lt_p384 _ _ hfy
            step as ⟨oc, hoc⟩
            rw [hpt, hfx, hfy, rinv_tomont _ hxp, rinv_tomont _ hyp] at hoc
            split
            · rename_i hon
              have hc : p384OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := hoc.mp hon
              simp only [WP.spec_ok, hc, ↓reduceIte]
              refine ⟨pt, rfl, ?_⟩
              rw [hpt]
              refine ⟨hfxp, hfyp, ?_⟩
              rw [hfx, hfy, rinv_tomont _ hxp, rinv_tomont _ hyp]
            · rename_i hon
              have hc : ¬ p384OnCurve (some (wordsNat x1.val, wordsNat y1.val)) :=
                fun h => hon (hoc.mpr h)
              simp [WP.spec_ok, hc]
          · simp only [hyp, iff_false] at hby
            have hon : ¬ p384OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := fun h => hyp h.2.1
            simp [hby, WP.spec_ok, hon]
        · simp only [hxp, iff_false] at hbx
          have hon : ¬ p384OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := fun h => hxp h.1
          simp [hbx, WP.spec_ok, hon]
      · have hlen : (bytes.len != i2) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h; apply hl
          have := congrArg UScalar.val h
          simp [Slice.len, hi2, hi1] at this; simpa [Slice.length] using this
        simp [hlen, hl, WP.spec_ok]
    · rename_i hne
      have h4 : b0 ≠ 4#u8 := fun h => hne (by rw [h]; exact UScalar.eq_of_val_eq rfl)
      simp [WP.spec_ok, h4]

/-! ## Scalar multiplication -/

theorem tripleNat6_append (a b : List U64) (ha : a.length = 12) (hb : b.length = 6) :
    tripleNat6 (a ++ b) = ((pairNat6 a).1, (pairNat6 a).2, wordsNat b) := by
  simp [tripleNat6, pairNat6, ha, hb, List.take_of_length_le, List.drop_append_of_le_length,
    List.take_append_of_le_length]

@[step]
theorem from_affine_spec (pt : mid.p384.AffineMontPoint) :
    mid.p384.JacobianMontPoint.from_affine pt ⦃ j =>
      tripleNat6 j.xyz.val = ((pairNat6 pt.xy.val).1, (pairNat6 pt.xy.val).2,
        feNat mid.p384.CURVE_ONE_MONT) ⦄ := by
  unfold mid.p384.JacobianMontPoint.from_affine core.default.DefaultArray.default
  step*
  · simp [mid.p384.JacobianMontPoint.XY]
  · simp [mid.p384.JacobianMontPoint.XY]
  · simp [s_post1, s1_post, mid.p384.JacobianMontPoint.XY, Slice.length]
  · simp [mid.p384.JacobianMontPoint.Z]
  · simp [mid.p384.JacobianMontPoint.Z]
  · simp [s3_post1, s4_post, mid.p384.JacobianMontPoint.Z, Slice.length]
  · have hp : (pt.xy.val).length = 12 := pt.xy.property
    have ho : (mid.p384.CURVE_ONE_MONT.val).length = 6 := mid.p384.CURVE_ONE_MONT.property
    rw [s3_post2, s5_post, s4_post, s2_post, s1_post, s_post2]
    have h18 : (Array.repeat 18#usize core.default.DefaultU64.default).val =
        [] ++ List.replicate 12 core.default.DefaultU64.default ++
          List.replicate 6 core.default.DefaultU64.default := by
      simp [Array.repeat]
    simp only [mid.p384.JacobianMontPoint.XY, mid.p384.JacobianMontPoint.Z, Array.val_to_slice, h18]
    rw [show (0#usize).val = ([] : List U64).length by simp,
      setSlice!_append _ _ _ _ (by simp [hp]), List.nil_append,
      show (12#usize).val = pt.xy.val.length by simp [hp],
      ← List.append_nil (pt.xy.val ++ List.replicate 6 _), setSlice!_append _ _ _ _ (by simp [ho]),
      List.append_nil, tripleNat6_append _ _ hp ho]

/-- An affine point in Montgomery form is the Jacobian point with Z one. -/
theorem represents_of_represents2 (P : nist.Point) (x y : Nat) (h : p384Represents2 P (x, y)) :
    p384Represents P (x, y, 2 ^ 384 % p384) := by
  obtain ⟨hx, hy, rfl⟩ := h
  refine ⟨hx, hy, Nat.mod_lt _ p384_pos, ?_⟩
  have h1 : p384RInv * (2 ^ 384 % p384) % p384 = 1 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm, p384RInv_spec.2]
  have hi : ((1 : ZMod p384) ^ 2)⁻¹ = 1 ∧ ((1 : ZMod p384) ^ 3)⁻¹ = 1 :=
    ⟨ZMod.inv_eq_of_mul_eq_one _ _ _ (by simp), ZMod.inv_eq_of_mul_eq_one _ _ _ (by simp)⟩
  simp only [nist.ofJacobian, h1, one_ne_zero, ↓reduceIte, Nat.cast_one, hi.1, hi.2, mul_one,
    ZMod.val_natCast, Nat.mod_mod]

@[step]
theorem multiply_spec (_h : Runs) (k : mid.p384.Scalar) (pt : mid.p384.AffineMontPoint) (P : nist.Point)
    (hP : p384OnCurve P) (hrep : p384Represents2 P (pairNat6 pt.xy.val)) :
    mid.p384.JacobianMontPoint.multiply k pt ⦃ j =>
      p384Represents (p384Pow P (wordsNat k.val)) (tripleNat6 j.xyz.val) ⦄ := by
  unfold mid.p384.JacobianMontPoint.multiply mid.p384.JacobianMontPoint.zero
  step as ⟨j0, hj0⟩
  step*
  apply a_post _ hP
  rw [hj0, CURVE_ONE_MONT_val]
  exact represents_of_represents2 _ _ _ hrep

@[step]
theorem jac_x_spec (j : mid.p384.JacobianMontPoint) :
    mid.p384.JacobianMontPoint.x j ⦃ fe => feNat fe = (tripleNat6 j.xyz.val).1 ⦄ := by
  unfold mid.p384.JacobianMontPoint.x
  have hl : (j.xyz.val).length = 18 := j.xyz.property
  step*
  · simp [mid.p384.JacobianMontPoint.X]
  · simp [mid.p384.JacobianMontPoint.X]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p384.JacobianMontPoint.X]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [feNat, ha, s_post, mid.p384.JacobianMontPoint.X, List.slice, tripleNat6]

@[step]
theorem jac_y_spec (j : mid.p384.JacobianMontPoint) :
    mid.p384.JacobianMontPoint.y j ⦃ fe => feNat fe = (tripleNat6 j.xyz.val).2.1 ⦄ := by
  unfold mid.p384.JacobianMontPoint.y
  have hl : (j.xyz.val).length = 18 := j.xyz.property
  step*
  · simp [mid.p384.JacobianMontPoint.Y]
  · simp [mid.p384.JacobianMontPoint.Y]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p384.JacobianMontPoint.Y]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [feNat, ha, s_post, mid.p384.JacobianMontPoint.Y, List.slice, tripleNat6]

@[step]
theorem jac_z_spec (j : mid.p384.JacobianMontPoint) :
    mid.p384.JacobianMontPoint.z j ⦃ fe => feNat fe = (tripleNat6 j.xyz.val).2.2 ⦄ := by
  unfold mid.p384.JacobianMontPoint.z
  have hl : (j.xyz.val).length = 18 := j.xyz.property
  step*
  · simp [mid.p384.JacobianMontPoint.Z]
  · simp [mid.p384.JacobianMontPoint.Z]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p384.JacobianMontPoint.Z]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [feNat, ha, s_post, mid.p384.JacobianMontPoint.Z, List.slice, tripleNat6]

/-- What `as_affine`'s arithmetic computes, in the field: the Montgomery
forms of x/z² and y/z³ for z's inverse `zi`, or zeros when z is zero and
`bignum_inv_p384` returns zero. -/
theorem affine_decode (X Y Z zi : Nat) (hz : p384RInv * Z % p384 % p384 = 0 → zi = 0)
    (hzi : p384RInv * Z % p384 % p384 ≠ 0 → p384RInv * Z % p384 * zi % p384 = 1) :
    let z2 := p384RInv * (2 ^ 384 * zi % p384) ^ 2 % p384
    let z3 := p384RInv * z2 * (2 ^ 384 * zi % p384) % p384
    (p384RInv * (p384RInv * X * z2 % p384) % p384, p384RInv * (p384RInv * Y * z3 % p384) % p384) =
      (nist.ofJacobian p384 (p384RInv * X % p384) (p384RInv * Y % p384) (p384RInv * Z % p384)).getD
        (0, 0) := by
  intro z2 z3
  have hRr := rinv_cast
  simp only [nist.ofJacobian]
  split_ifs with h0
  · rw [Nat.mod_eq_of_lt (Nat.mod_lt _ p384_pos)] at hz
    have := hz (by rw [h0])
    simp [z2, z3, this]
  · rw [Nat.mod_eq_of_lt (Nat.mod_lt _ p384_pos)] at hzi
    have hm := hzi h0
    generalize p384RInv * Z % p384 = zd at hm h0
    have hinv : ((zd : ZMod p384) ^ 2)⁻¹ = (zi : ZMod p384) ^ 2 ∧
        ((zd : ZMod p384) ^ 3)⁻¹ = (zi : ZMod p384) ^ 3 := by
      have h1 : (zd : ZMod p384) * zi = 1 := by
        have := congrArg (fun n : Nat => (n : ZMod p384)) hm
        simpa only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] using this
      constructor
      · exact ZMod.inv_eq_of_mul_eq_one _ _ _ (by rw [← mul_pow, h1, one_pow])
      · exact ZMod.inv_eq_of_mul_eq_one _ _ _ (by rw [← mul_pow, h1, one_pow])
    rw [hinv.1, hinv.2, Option.getD_some]
    simp only [z2, z3]
    generalize (2 : Nat) ^ 384 = R at hRr ⊢
    refine Prod.ext ?_ ?_ <;> simp only <;>
      rw [← ZMod.val_natCast_of_lt (Nat.mod_lt _ p384_pos)] <;> congr 1 <;> push_cast [ZMod.natCast_mod]
    · linear_combination ((p384RInv : ZMod p384) * X * zi ^ 2 * (R * p384RInv + 1)) * hRr
    · linear_combination ((p384RInv : ZMod p384) * Y * zi ^ 3 *
        (R ^ 2 * p384RInv ^ 2 + R * p384RInv + 1)) * hRr

@[step]
theorem as_affine_spec (_h : Runs) (j : mid.p384.JacobianMontPoint) (Q : nist.Point)
    (hrep : p384Represents Q (tripleNat6 j.xyz.val)) :
    mid.p384.JacobianMontPoint.as_affine j ⦃ a =>
      (pairNat6 a.xy.val).1 < p384 ∧ (pairNat6 a.xy.val).2 < p384 ∧
        (p384RInv * (pairNat6 a.xy.val).1 % p384, p384RInv * (pairNat6 a.xy.val).2 % p384) =
          Q.getD (0, 0) ⦄ := by
  obtain ⟨hX, hY, hZ, rfl⟩ := hrep
  unfold mid.p384.JacobianMontPoint.as_affine mid.p384.JacobianMontPoint.as_affine_by
  step as ⟨z, hz⟩
  have hz' : feNat z < p384 := by rw [hz]; exact hZ
  step as ⟨zd, hzd⟩
  step as ⟨zi, hzi1, hzi2, hzi3⟩
  step as ⟨zm, hzm⟩
  have hzm' := fe_lt_p384 _ _ hzm
  step as ⟨z2, hz2⟩
  have hz2' := fe_lt_p384 _ _ hz2
  step as ⟨z3, hz3⟩
  have hz3' := fe_lt_p384 _ _ hz3
  step as ⟨x, hx⟩
  have hx'' : feNat x < p384 := by rw [hx]; exact hX
  step as ⟨x', hx'⟩
  step as ⟨y, hy⟩
  have hy'' : feNat y < p384 := by rw [hy]; exact hY
  step as ⟨y', hy'⟩
  step as ⟨a, ha⟩
  rw [ha]
  refine ⟨fe_lt_p384 _ _ hx', fe_lt_p384 _ _ hy', ?_⟩
  rw [hx', hy', hz3, hz2, hzm, hx, hy]
  rw [hzd, hz] at hzi2 hzi3
  exact affine_decode _ _ _ _ hzi2 hzi3

theorem not_onCurve_zero : ¬ p384OnCurve (some (0, 0)) := by
  simp [p384OnCurve, nist.OnCurve, p384, b384]

@[step]
theorem diffie_hellman_spec (h : Runs) (k : mid.p384.PrivateKey) (peer : mid.p384.PublicKey)
    (P : nist.Point) (hP : p384OnCurve P) (hrep : p384Represents2 P (pairNat6 peer.point.xy.val)) :
    mid.p384.PrivateKey.diffie_hellman k peer ⦃ r =>
      match p384Pow P (wordsNat k.scalar.val) with
      | some (x, y) =>
        if p384OnCurve (some (x, y)) then ∃ s, r = .Ok s ∧ beNat s.val = x else r = .Err .Fault
      | none => r = .Err .Fault ⦄ := by
  unfold mid.p384.PrivateKey.diffie_hellman low.ct.into_public
  step
  step with multiply_spec h _ _ P hP hrep as ⟨j, hj⟩
  step with as_affine_spec h j _ hj as ⟨q, hqx, hqy, hq⟩
  step as ⟨b, hb⟩
  rw [hq] at hb
  rcases hQ : p384Pow P (wordsNat k.scalar.val) with _ | ⟨x, y⟩
  · rw [hQ] at hb
    simp only [Option.getD_none, not_onCurve_zero, iff_false] at hb
    simp [hb]
  · rw [hQ] at hb hq
    simp only [Option.getD_some] at hb hq
    by_cases hc : p384OnCurve (some (x, y))
    · have hbt : b = true := hb.mpr hc
      simp only [hbt, hc, ↓reduceIte]
      step as ⟨fx, hfx⟩
      have hfx' : feNat fx < p384 := by rw [hfx]; exact hqx
      step as ⟨dx, hdx⟩
      step as ⟨sb, hsb⟩
      refine ⟨sb, rfl, ?_⟩
      rw [hsb, ← feNat, hdx, hfx]
      exact congrArg Prod.fst hq
    · have hbf : b = false := by simpa [hc] using hb
      simp [hbf, hc]

theorem public_from_x962_spec (h : Runs) (bytes : Slice U8) :
    mid.p384.PublicKey.from_x962_uncompressed bytes ⦃ r =>
      match bytes.val.head? with
      | none => r = .Err (.KeyRejected .WrongLength)
      | some b0 =>
        if b0 = 4#u8 then
          if bytes.length = 97 then
            if p384OnCurve (some (p384Coords bytes.val)) then
              ∃ pk, r = .Ok pk ∧ p384Represents2 (some (p384Coords bytes.val)) (pairNat6 pk.point.xy.val)
            else r = .Err (.KeyRejected .NotOnCurve)
          else r = .Err (.KeyRejected .WrongLength)
        else r = .Err (.KeyRejected .Compressed) ⦄ := by
  unfold mid.p384.PublicKey.from_x962_uncompressed
  step
  step with from_x962_spec h bytes as ⟨r, hr⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rcases hb : bytes.val.head? with _ | b0
  · simp only [hb] at hr
    subst hr
    simp
  · simp only [hb] at hr ⊢
    by_cases h4 : b0 = 4#u8 <;> simp only [h4, ↓reduceIte] at hr ⊢
    · by_cases hl : bytes.length = 97 <;> simp only [hl, ↓reduceIte] at hr ⊢
      · by_cases hon : p384OnCurve (some (p384Coords bytes.val)) <;> simp only [hon, ↓reduceIte] at hr ⊢
        · obtain ⟨pt, rfl, hpt⟩ := hr
          simp [hpt]
        · subst hr; simp
      · subst hr; simp
    · subst hr; simp

theorem agree_spec (h : Runs) (k : mid.p384.PrivateKey) (peer : Slice U8) :
    high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.agree k peer ⦃ r =>
      p384Agreement (wordsNat k.scalar.val) peer.val r ⦄ := by
  unfold high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.agree p384Agreement
  step with public_from_x962_spec h peer as ⟨r, hr⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rcases hb : peer.val.head? with _ | b0
  · simp only [hb] at hr
    subst hr
    simp
  · simp only [hb] at hr ⊢
    by_cases h4 : b0 = 4#u8 <;> simp only [h4, ↓reduceIte] at hr ⊢
    · by_cases hl : peer.length = 97 <;> simp only [hl, ↓reduceIte] at hr ⊢
      · by_cases hon : p384OnCurve (some (p384Coords peer.val)) <;> simp only [hon, ↓reduceIte] at hr ⊢
        · obtain ⟨pk, rfl, hpk⟩ := hr
          simp only
          step with diffie_hellman_spec h k pk _ hon hpk as ⟨r1, hr1⟩
          rcases hq : p384Pow (some (p384Coords peer.val)) (wordsNat k.scalar.val) with _ | ⟨x, y⟩ <;>
            simp only [hq] at hr1 ⊢
          · subst hr1; simp
          · by_cases hc : p384OnCurve (some (x, y)) <;> simp only [hc, ↓reduceIte] at hr1 ⊢
            · obtain ⟨s, rfl, hs⟩ := hr1
              simp [hs]
            · subst hr1; simp
        · subst hr; simp
      · subst hr; simp
    · subst hr; simp

end P384

open P384 in
/-- P-384 ECDH with a key whose scalar is `k`'s: `p384Agreement`. -/
theorem p384_agree (h : Runs) (key : high.agreement.PrivateKey)
    (k : high.agreement.Keyed high.curve.P384 mid.p384.PrivateKey) (hk : key.«private» = .P384 k)
    (peer : Slice U8) :
    high.agreement.PrivateKey.agree key peer ⦃ r =>
      p384Agreement (wordsNat k.key.scalar.val) peer.val r ⦄ := by
  unfold high.agreement.PrivateKey.agree high.agreement.Keyed.agree
  rw [hk]
  step with agree_spec h k.key peer as ⟨r, hr⟩
  rcases r with s | e <;> simpa using hr

/-- The shared secret's bytes are the ones `p384_agree` states. -/
theorem p384_shared_secret (s : mid.p384.SharedSecret) :
    high.agreement.SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref (.P384 s) ⦃ b =>
      b.val = s.val ⦄ := by
  simp [high.agreement.SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref, Array.val_to_slice]

end rind.x86_64
