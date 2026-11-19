import Rind.X86_64.S2nBignum
import Rind.X86_64.VgP256
import Rind.X86_64.Dispatch
import Rind.Bytes
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result rind.spec

/-!
# P-256 ECDH's agreement, proven from rind's agreement API to s2n-bignum's contracts

`p256_agree` states what the agreement API returns for `ECDH_P256`, in terms
of `p256Pow`, HOL Light's `group_pow p256_group`, through the dispatch
`Rind.X86_64.Dispatch` models. rind keeps points in Montgomery form, which
`mont_on_curve` relates to the curve equation, and s2n-bignum's
`p256_scalarmul` takes and returns plain coordinates. `admin/prove` writes the
aarch64 proof from this file by renaming the target. Key generation, which
multiplies the generator, is `Rind.X86_64.P256`'s.
-/

namespace rind.x86_64

/-! ## What the theorems state -/

/-- pyca/verified-garbage's P-256 checks return, reading no input: `check`,
for ECDH and verification, and `check_public_key`, for the public key's
derivation. Where one passes, P-256 runs VG's routine, whose contract
`Rind.X86_64.VgP256` states, and otherwise rind's own; the theorems cover
both. -/
def RunsP256 : Prop :=
  (∃ t, low.x86_64.p256_vg.P256.check = ok t) ∧ ∃ t, low.x86_64.p256_vg.P256.check_public_key = ok t

/-- The coordinates an encoded point names, read big-endian after its tag byte. -/
def x962Coords (bytes : List U8) : Nat × Nat :=
  (beNat (bytes.slice 1 33), beNat (bytes.slice 33 65))

/-- P-256 ECDH's outcome, for scalar `k` and the peer's encoded key: refused
unless it is an X9.62 uncompressed point on the curve, with coordinates below
`p256`, and otherwise the x-coordinate of `k` times that point, or a fault
unless that is a finite point on the curve. -/
def p256Agreement (k : Nat) (peer : List U8) (r : core.result.Result high.agreement.Secret error.Error) :
    Prop :=
  match peer.head? with
  | none => r = .Err (.KeyRejected .WrongLength)
  | some b0 =>
    if b0 = 4#u8 then
      if peer.length = 65 then
        if p256OnCurve (some (x962Coords peer)) then
          match p256Pow (some (x962Coords peer)) k with
          | some (x, y) =>
            if p256OnCurve (some (x, y)) then ∃ s, r = .Ok (.P256 s) ∧ beNat s.val = x
            else r = .Err .Fault
          | none => r = .Err .Fault
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength)
    else r = .Err (.KeyRejected .Compressed)

/-! The P-256 lemmas' own namespace keeps their names apart from X25519's. -/
namespace P256

/-! ## Byte and limb conversions, `mid::util` -/

theorem be_to_u64x4_loop_spec (b : Std.Array U8 32#usize) (iter : core.ops.range.Range Std.Usize)
    (r : Std.Array U64 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hr : ∀ i < iter.start.val, (r.val[i]!).val = beNat (b.val.slice (8 * (3 - i)) (8 * (4 - i)))) :
    mid.util.big_endian_to_u64x4_loop iter b r ⦃ r' =>
      ∀ i < 4, (r'.val[i]!).val = beNat (b.val.slice (8 * (3 - i)) (8 * (4 - i))) ⦄ := by
  unfold mid.util.big_endian_to_u64x4_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      ∀ i < x.1.start.val, (x.2.val[i]!).val = beNat (b.val.slice (8 * (3 - i)) (8 * (4 - i))))
  · rintro ⟨it, r⟩ ⟨hs, he, hr⟩
    simp only at hs he hr ⊢
    unfold mid.util.big_endian_to_u64x4_loop.body
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
        have hi : i5.val = beNat (b.val.slice (8 * (3 - it.start.val)) (8 * (4 - it.start.val))) := by
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
theorem be_to_u64x4_spec (b : Std.Array U8 32#usize) :
    mid.util.big_endian_to_u64x4 b ⦃ w => wordsNat w.val = beNat b.val ⦄ := by
  unfold mid.util.big_endian_to_u64x4
  apply WP.spec_mono (be_to_u64x4_loop_spec b _ _ (by simp) (by simp) (by simp))
  intro w hw
  rw [wordsNat_four _ w.property, beNat_32 _ b.property, hw 0 (by omega), hw 1 (by omega),
    hw 2 (by omega), hw 3 (by omega)]

/-- The bytes `u64::to_be_bytes` writes. -/
def beBytes (w : U64) : List U8 := w.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)

theorem length_beBytes (w : U64) : (beBytes w).length = 8 := by
  simp [beBytes]

theorem u64x4_to_be_loop_spec (v : Std.Array U64 4#usize) (iter : core.ops.range.Range Std.Usize)
    (r : Std.Array U8 32#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hr : r.val = List.replicate (8 * (4 - iter.start.val)) 0#u8 ++
      ((v.val.take iter.start.val).reverse.flatMap beBytes)) :
    mid.util.u64x4_to_big_endian_loop iter v r ⦃ r' =>
      r'.val = v.val.reverse.flatMap beBytes ⦄ := by
  unfold mid.util.u64x4_to_big_endian_loop
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      x.2.val = List.replicate (8 * (4 - x.1.start.val)) 0#u8 ++
        ((v.val.take x.1.start.val).reverse.flatMap beBytes))
  · rintro ⟨it, r⟩ ⟨hs, he, hr⟩
    simp only at hs he hr ⊢
    unfold mid.util.u64x4_to_big_endian_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      have hv : (v.val).length = 4 := v.property
      step*
      · rw [s_post1, s1_post]
        simp [i4_post, i3_post, i2_post, i1_post, i_post]
        omega
      · refine ⟨by omega, by simp [he1, he], ?_, by omega⟩
        have hs1 : s1.val = beBytes (v.val[it.start.val]) := by
          rw [s1_post, Array.val_to_slice, a_post, i5_post, beBytes]
        rw [s_post2, s2_post, hs1, hr, show 8 * (4 - it.start.val) = 8 * (3 - it.start.val) + 8 by omega,
          ← List.replicate_append_replicate, show i2.val = (List.replicate (8 * (3 - it.start.val)) 0#u8).length by
            simp [i2_post, i1_post, i_post]; omega,
          setSlice!_append _ _ _ _ (by simp [length_beBytes]), hst,
          show 8 * (4 - (it.start.val + 1)) = 8 * (3 - it.start.val) by omega]
        simp only [List.append_assoc, List.append_cancel_left_eq]
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.reverse_append, List.flatMap_append]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have h4 : it.start.val = 4 := by omega
      have hv : (v.val).length = 4 := v.property
      rw [hr, h4, List.take_of_length_le (by omega)]
      simp
  · exact ⟨hs, he, hr⟩

theorem beNat_beBytes (w : U64) : beNat (beBytes w) = w.val := beNat_toBEBytes w

@[step]
theorem u64x4_to_be_spec (v : Std.Array U64 4#usize) :
    mid.util.u64x4_to_big_endian v ⦃ b => beNat b.val = wordsNat v.val ⦄ := by
  unfold mid.util.u64x4_to_big_endian
  apply WP.spec_mono (u64x4_to_be_loop_spec v _ _ (by simp) (by simp) (by simp))
  intro b hb
  rw [hb]
  have hv : (v.val).length = 4 := v.property
  generalize v.val = l at hv ⊢
  match l, hv with
  | [a, b, c, d], _ =>
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, beNat_append, length_beBytes,
      beNat_beBytes, wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil,
      List.length_append]
    ring

@[step]
theorem be_slice_to_u64x4_spec (s : Slice U8) :
    mid.util.big_endian_slice_to_u64x4 s ⦃ o =>
      if s.length = 32 then ∃ w, o = some w ∧ wordsNat w.val = beNat s.val else o = none ⦄ := by
  unfold mid.util.big_endian_slice_to_u64x4
  step*
  rcases r with a | _
  · obtain ⟨ha, hl⟩ := r_post
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    step*
  · simp [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, r_post]

theorem be_any_size_32_spec (s : Slice U8) (h : s.length = 32) :
    mid.util.big_endian_slice_any_size_to_u64x4 s ⦃ o =>
      ∃ w, o = some w ∧ wordsNat w.val = beNat s.val ⦄ := by
  unfold mid.util.big_endian_slice_any_size_to_u64x4
  have hl : s.len = 32#usize := by
    apply UScalar.eq_of_val_eq; simpa [Slice.len, Slice.length] using h
  simp only [core.array.TryFromSharedArraySlice.try_from, hl, ↓reduceDIte]
  step as ⟨w, hw⟩
  simp [hw]

/-! ## Field elements and points, `mid::p256` -/

/-- The number a field element's limbs encode. -/
abbrev feNat (fe : mid.p256.FieldElement) : Nat := wordsNat fe.val

@[step]
theorem as_mont_spec (_h : Runs) (fe : mid.p256.FieldElement) :
    mid.p256.FieldElement.as_mont fe ⦃ r => feNat r = 2 ^ 256 * feNat fe % p256 ⦄ := by
  unfold mid.p256.FieldElement.as_mont mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem demont_spec (_h : Runs) (fe : mid.p256.FieldElement) (h : feNat fe < p256) :
    mid.p256.FieldElement.demont fe ⦃ r => feNat r = p256RInv * feNat fe % p256 ⦄ := by
  unfold mid.p256.FieldElement.demont mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

@[step]
theorem fe_add_spec (a b : mid.p256.FieldElement) (ha : feNat a < p256) (hb : feNat b < p256) :
    mid.p256.FieldElement.add a b ⦃ r => feNat r = (feNat a + feNat b) % p256 ⦄ := by
  unfold mid.p256.FieldElement.add mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*

theorem p256_lt : p256 < 2 ^ 256 := by simp only [p256]; decide

@[step]
theorem mont_mul_spec (_h : Runs) (a b : mid.p256.FieldElement) (ha : feNat a < p256) (hb : feNat b < p256) :
    mid.p256.FieldElement.mont_mul a b ⦃ r => feNat r = p256RInv * feNat a * feNat b % p256 ⦄ := by
  unfold mid.p256.FieldElement.mont_mul mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  exact a_post (le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb)
    (Nat.mul_le_mul_right _ (le_of_lt p256_lt))))

@[step]
theorem mont_sqr_spec (_h : Runs) (a : mid.p256.FieldElement) (ha : feNat a < p256) :
    mid.p256.FieldElement.mont_sqr a ⦃ r => feNat r = p256RInv * feNat a ^ 2 % p256 ⦄ := by
  unfold mid.p256.FieldElement.mont_sqr mid.p256.FieldElement.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  step*
  exact a_post (by
    rw [pow_two]
    exact le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' ha ha)
      (Nat.mul_le_mul_right _ (le_of_lt p256_lt))))

@[step]
theorem point_x_spec (pt : mid.p256.AffineMontPoint) :
    mid.p256.AffineMontPoint.x pt ⦃ fe => fe.val = pt.xy.val.take 4 ⦄ := by
  unfold mid.p256.AffineMontPoint.x
  have hl : (pt.xy.val).length = 8 := pt.xy.property
  step*
  · simp [mid.p256.AffineMontPoint.X]
  · simp [mid.p256.AffineMontPoint.X]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.AffineMontPoint.X]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.AffineMontPoint.X, List.slice]

@[step]
theorem point_y_spec (pt : mid.p256.AffineMontPoint) :
    mid.p256.AffineMontPoint.y pt ⦃ fe => fe.val = pt.xy.val.drop 4 ⦄ := by
  unfold mid.p256.AffineMontPoint.y
  have hl : (pt.xy.val).length = 8 := pt.xy.property
  step*
  · simp [mid.p256.AffineMontPoint.Y]
  · simp [mid.p256.AffineMontPoint.Y]
  · rcases r with a | _
    · exact ⟨a, rfl⟩
    · exact absurd (by simp [s_post1, mid.p256.AffineMontPoint.Y]) r_post
  · subst r_post
    obtain ⟨ha, -⟩ := r_post
    simp [ha, s_post, mid.p256.AffineMontPoint.Y, List.slice, List.take_of_length_le, hl]

@[step]
theorem from_xy_spec (x y : mid.p256.FieldElement) :
    mid.p256.AffineMontPoint.from_xy x y ⦃ pt => pt.xy.val = x.val ++ y.val ⦄ := by
  unfold mid.p256.AffineMontPoint.from_xy mid.p256.AffineMontPoint.Insts.CoreDefaultDefault.default
    core.default.DefaultArray.default
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index]
  step*
  · simp [mid.p256.AffineMontPoint.X]
  · simp [mid.p256.AffineMontPoint.X]
  · simp [s_post1, mid.p256.AffineMontPoint.X]
  · simp [mid.p256.AffineMontPoint.Y]
  · simp [mid.p256.AffineMontPoint.Y]
  · simp [s3_post1, mid.p256.AffineMontPoint.Y]
  · have hx : (x.val).length = 4 := x.property
    have hy : (y.val).length = 4 := y.property
    rw [s3_post2, s5_post, s2_post, s_post2]
    have h8 : (Array.repeat 8#usize core.default.DefaultU64.default).val =
        [] ++ List.replicate 4 core.default.DefaultU64.default ++
          List.replicate 4 core.default.DefaultU64.default := by
      simp [Array.repeat]
    simp only [mid.p256.AffineMontPoint.X, mid.p256.AffineMontPoint.Y, Array.val_to_slice, h8]
    rw [show (0#usize).val = ([] : List U64).length by simp,
      setSlice!_append _ _ _ _ (by simp [hx]), List.nil_append,
      show (4#usize).val = x.val.length by simp [hx],
      ← List.append_nil (x.val ++ List.replicate 4 _), setSlice!_append _ _ _ _ (by simp [hy])]
    simp

theorem CURVE_A_MONT_val : feNat mid.p256.CURVE_A_MONT = 2 ^ 256 * (p256 - 3) % p256 := by
  simp only [feNat, mid.p256.CURVE_A_MONT, Array.make, Array.from_val, wordsNat, p256]
  decide

theorem CURVE_B_MONT_val : feNat mid.p256.CURVE_B_MONT = 2 ^ 256 * b256 % p256 := by
  simp only [feNat, mid.p256.CURVE_B_MONT, Array.make, Array.from_val, wordsNat, p256, b256]
  decide

/-- rind's curve check, in Montgomery form, is the curve equation on the
coordinates it encodes. -/
theorem mont_on_curve (X Y : Nat) :
    p256RInv * Y ^ 2 % p256 =
        (p256RInv * ((p256RInv * X ^ 2 % p256 + 2 ^ 256 * (p256 - 3) % p256) % p256) * X % p256 +
          2 ^ 256 * b256 % p256) % p256 ↔
      p256OnCurve (some (p256RInv * X % p256, p256RInv * Y % p256)) := by
  have hp : 0 < p256 := by simp [p256]
  have hRr : ((2 ^ 256 : Nat) : ZMod p256) * (p256RInv : ZMod p256) = 1 := by
    have := congrArg (fun n : Nat => (n : ZMod p256)) p256RInv_spec.2
    simpa only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] using this
  generalize (2 : Nat) ^ 256 = R at hRr ⊢
  simp only [p256OnCurve, nist.OnCurve, Nat.mod_lt _ hp, true_and]
  rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff']
  push_cast [ZMod.natCast_mod]
  constructor
  · intro h
    linear_combination (p256RInv : ZMod p256) * h +
      (((p256 - 3 : Nat) : ZMod p256) * p256RInv * X + b256) * hRr
  · intro g
    linear_combination (R : ZMod p256) * g -
      ((p256RInv : ZMod p256) * Y ^ 2 - (p256RInv : ZMod p256) ^ 2 * X ^ 3) * hRr

theorem pairNat_drop (l : List U64) (h : l.length = 8) : (pairNat l).2 = wordsNat (l.drop 4) := by
  simp [pairNat, List.take_of_length_le, h]

theorem fe_lt_p256 (fe : mid.p256.FieldElement) (n : Nat) (h : feNat fe = n % p256) : feNat fe < p256 := by
  rw [h]; exact Nat.mod_lt _ (by simp [p256])

@[step]
theorem on_curve_spec (_h : Runs) (pt : mid.p256.AffineMontPoint) (hx : (pairNat pt.xy.val).1 < p256)
    (hy : (pairNat pt.xy.val).2 < p256) :
    mid.p256.AffineMontPoint.on_curve pt ⦃ b =>
      (b ↔ p256OnCurve (some (p256RInv * (pairNat pt.xy.val).1 % p256,
        p256RInv * (pairNat pt.xy.val).2 % p256))) ⦄ := by
  have hl : (pt.xy.val).length = 8 := pt.xy.property
  rw [pairNat_drop _ hl] at hy ⊢
  simp only [pairNat] at hx ⊢
  unfold mid.p256.AffineMontPoint.on_curve
  step as ⟨x, hxv⟩
  have hx' : feNat x < p256 := by simpa [feNat, hxv] using hx
  step as ⟨r0, hr0⟩
  have hA : feNat mid.p256.CURVE_A_MONT < p256 := by rw [CURVE_A_MONT_val]; exact Nat.mod_lt _ (by simp [p256])
  step as ⟨r1, hr1⟩
  step as ⟨r2, hr2⟩
  have hB : feNat mid.p256.CURVE_B_MONT < p256 := by rw [CURVE_B_MONT_val]; exact Nat.mod_lt _ (by simp [p256])
  step as ⟨r3, hr3⟩
  step as ⟨y, hyv⟩
  have hy' : feNat y < p256 := by simpa [feNat, hyv] using hy
  step as ⟨l, hl'⟩
  step*
  have hX : feNat x = wordsNat (pt.xy.val.take 4) := by simp [feNat, hxv]
  have hY : feNat y = wordsNat (pt.xy.val.drop 4) := by simp [feNat, hyv]
  rw [b_post, s_post, s1_post, Array.val_to_slice, Array.val_to_slice, decide_eq_true_iff,
    ← mont_on_curve, ← hX, ← hY, ← CURVE_A_MONT_val, ← CURVE_B_MONT_val]
  simp only [feNat] at hl' hr3 hr2 hr1 hr0
  rw [hl', hr3, hr2, hr1, hr0]

theorem pairNat_append (a b : List U64) (ha : a.length = 4) (hb : b.length = 4) :
    pairNat (a ++ b) = (wordsNat a, wordsNat b) := by
  simp [pairNat, ha, List.take_of_length_le, hb]

theorem rinv_tomont (x : Nat) (hx : x < p256) : p256RInv * (2 ^ 256 * x % p256) % p256 = x := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod,
    Nat.mul_comm p256RInv, p256RInv_spec.2, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hx]

/-- The limbs of `CURVE_PRIME`, most significant last. -/
theorem CURVE_PRIME_val : mid.p256.CURVE_PRIME.val =
    [18446744073709551615#u64, 4294967295#u64, 0#u64, 18446744069414584321#u64] := by
  simp [mid.p256.CURVE_PRIME, Array.make]

/-- Comparing limbs from the top, the first that differ decide which number
is smaller. -/
theorem lt_p256_of_top (v : List U64) (hv : v.length = 4) (s : Nat) (hs : s < 4)
    (heq : ∀ k < s, v[3 - k]! = mid.p256.CURVE_PRIME.val[3 - k]!)
    (hne : v[3 - s]! ≠ mid.p256.CURVE_PRIME.val[3 - s]!) :
    wordsNat v < p256 ↔ v[3 - s]!.val < (mid.p256.CURVE_PRIME.val[3 - s]!).val := by
  match v, hv with
  | [a, b, c, d], _ =>
    have ha := a.hBounds
    have hb := b.hBounds
    have hc := c.hBounds
    have hd := d.hBounds
    simp only [UScalarTy.numBits] at ha hb hc hd
    simp only [CURVE_PRIME_val, UScalar.eq_equiv] at heq hne ⊢
    simp only [wordsNat, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil, p256]
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl
    · simp at hne ⊢; omega
    · have e3 := heq 0 (by omega)
      simp at hne e3 ⊢; omega
    · have e3 := heq 0 (by omega)
      have e2 := heq 1 (by omega)
      simp at hne e3 e2 ⊢; omega
    · have e3 := heq 0 (by omega)
      have e2 := heq 1 (by omega)
      have e1 := heq 2 (by omega)
      simp at hne e3 e2 e1 ⊢; omega

theorem getElem_eq_getElem! {α : Type _} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i] = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wordsNat_CURVE_PRIME : wordsNat mid.p256.CURVE_PRIME.val = p256 := by
  simp only [CURVE_PRIME_val, wordsNat, p256]; decide

theorem below_p_loop_spec (v : Std.Array U64 4#usize) (iter : core.ops.range.Range Std.Usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (heq : ∀ k < iter.start.val, v.val[3 - k]! = mid.p256.CURVE_PRIME.val[3 - k]!) :
    mid.p256.public_below_p_loop
      iter v ⦃ b => (b ↔ wordsNat v.val < p256) ⦄ := by
  have hv : (v.val).length = 4 := v.property
  unfold mid.p256.public_below_p_loop
  apply loop.spec_decr_nat (fun x => 4 - x.start.val)
    (fun x => x.start.val ≤ 4 ∧ x.end.val = 4 ∧
      ∀ k < x.start.val, v.val[3 - k]! = mid.p256.CURVE_PRIME.val[3 - k]!)
  · rintro it ⟨hs, he, heq⟩
    unfold mid.p256.public_below_p_loop.body
    step as ⟨o, iter1, ho, he1⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      simp only
      step*
      · rename_i hne
        have hj : j.val < 4 := by omega
        have hne' : v.val[3 - it.start.val]! ≠ mid.p256.CURVE_PRIME.val[3 - it.start.val]! := by
          rw [← j_post, ← getElem_eq_getElem! _ _ (by omega), ← getElem_eq_getElem! _ _ (by simp [CURVE_PRIME_val]; omega),
            ← i1_post, ← i2_post]
          simpa using hne
        rw [lt_p256_of_top v.val hv _ (by omega) heq hne', decide_eq_true_iff, UScalar.lt_equiv, i1_post,
          i2_post, ← j_post, getElem_eq_getElem! _ _ (by omega),
          getElem_eq_getElem! _ _ (by simp [CURVE_PRIME_val]; omega)]
      · rename_i heq1
        refine ⟨by omega, by simp [he1, he], ?_, by omega⟩
        intro k hk
        by_cases hks : k = it.start.val
        · subst hks
          rw [← j_post, ← getElem_eq_getElem! _ _ (by omega), ← getElem_eq_getElem! _ _ (by simp [CURVE_PRIME_val]; omega),
            ← i1_post, ← i2_post]
          exact UScalar.eq_of_val_eq (by simpa using heq1)
        · exact heq k (by omega)
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_lt]
      have hall : v.val = mid.p256.CURVE_PRIME.val := by
        apply List.ext_getElem! (by simp [hv, CURVE_PRIME_val])
        intro n
        by_cases hn : n < 4
        · have := heq (3 - n) (by omega)
          rwa [show 3 - (3 - n) = n by omega] at this
        · simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega : v.val.length ≤ n),
            List.getElem?_eq_none (by simp [CURVE_PRIME_val]; omega : mid.p256.CURVE_PRIME.val.length ≤ n)]
      rw [hall, wordsNat_CURVE_PRIME]
  · exact ⟨hs, he, heq⟩

@[step]
theorem below_p_spec (v : Std.Array U64 4#usize) :
    mid.p256.public_below_p v ⦃ b => (b ↔ wordsNat v.val < p256) ⦄ :=
  below_p_loop_spec v _ (by simp) (by simp) (by simp)

theorem from_x962_spec (_h : Runs) (bytes : Slice U8) :
    mid.p256.AffineMontPoint.from_x962_uncompressed bytes ⦃ r =>
      match bytes.val.head? with
      | none => r = .Err (.KeyRejected .WrongLength)
      | some b0 =>
        if b0 = 4#u8 then
          if bytes.length = 65 then
            if p256OnCurve (some (x962Coords bytes.val)) then
              ∃ pt, r = .Ok pt ∧ p256Represents2 (some (x962Coords bytes.val)) (pairNat pt.xy.val)
            else r = .Err (.KeyRejected .NotOnCurve)
          else r = .Err (.KeyRejected .WrongLength)
        else r = .Err (.KeyRejected .Compressed) ⦄ := by
  unfold mid.p256.AffineMontPoint.from_x962_uncompressed
  simp only [core.slice.Slice.first, core.convert.IntoFrom.into,
    error.Error.Insts.CoreConvertFromKeyFormatError.from]
  rcases hb : bytes.val.head? with _ | b0
  · simp
  · simp only [bind_ok]
    split
    · have h4 : (4#8#uscalar : U8) = 4#u8 := UScalar.eq_of_val_eq rfl
      simp only [h4, ↓reduceIte]
      simp only [mid.p256.PublicKey.BYTES, mid.p256.FieldElement.BYTES]
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      by_cases hl : bytes.length = 65
      · have hlen : (bytes.len != i2) = false := by
          simp only [bne_eq_false_iff_eq]
          apply UScalar.eq_of_val_eq
          simp [Slice.len, hi2, hi1]; simpa [Slice.length] using hl
        simp only [hlen, Bool.false_eq_true, ↓reduceIte, hl]
        step as ⟨_, xy, _, _, _, hxy⟩
        step as ⟨x, y, hxl, _, hx, hy⟩
        have hyl : y.length = 32 := by
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
        have hc : x962Coords bytes.val = (wordsNat x1.val, wordsNat y1.val) := by
          rw [hx1, hy1, hx, hy, hxy, x962Coords]
          simp only [List.slice, List.drop_drop]
          simp [Slice.length] at hl
          congr 2
          rw [List.take_of_length_le (by simp; omega)]
        rw [hc]
        step as ⟨bx, hbx⟩
        by_cases hxp : wordsNat x1.val < p256
        · simp only [hxp, iff_true] at hbx
          simp only [hbx, ↓reduceIte]
          step as ⟨by', hby⟩
          by_cases hyp : wordsNat y1.val < p256
          · simp only [hyp, iff_true] at hby
            simp only [hby, ↓reduceIte]
            step as ⟨fx, hfx⟩
            step as ⟨fy, hfy⟩
            step as ⟨pt, hpt⟩
            have hpn : pairNat pt.xy.val = (feNat fx, feNat fy) := by
              rw [hpt, pairNat_append _ _ fx.property fy.property]
            have hfxp : feNat fx < p256 := fe_lt_p256 _ _ hfx
            have hfyp : feNat fy < p256 := fe_lt_p256 _ _ hfy
            step as ⟨oc, hoc⟩
            rw [hpn, hfx, hfy, rinv_tomont _ hxp, rinv_tomont _ hyp] at hoc
            split
            · rename_i hon
              have hc : p256OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := hoc.mp hon
              simp only [WP.spec_ok, hc, ↓reduceIte]
              refine ⟨pt, rfl, ?_⟩
              rw [hpn]
              refine ⟨hfxp, hfyp, ?_⟩
              rw [hfx, hfy, rinv_tomont _ hxp, rinv_tomont _ hyp]
            · rename_i hon
              have hc : ¬ p256OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := fun h => hon (hoc.mpr h)
              simp [WP.spec_ok, hc]
          · simp only [hyp, iff_false] at hby
            have hon : ¬ p256OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := fun h => hyp h.2.1
            simp [hby, WP.spec_ok, hon]
        · simp only [hxp, iff_false] at hbx
          have hon : ¬ p256OnCurve (some (wordsNat x1.val, wordsNat y1.val)) := fun h => hxp h.1
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

theorem tomont_mod (x : Nat) : 2 ^ 256 * (x % p256) % p256 = 2 ^ 256 * x % p256 := by
  rw [Nat.mul_mod, Nat.mul_mod (2 ^ 256) x, Nat.mod_mod]

theorem rinv_tomont_mod (x : Nat) : p256RInv * (2 ^ 256 * x % p256) % p256 = x % p256 := by
  rw [← tomont_mod, rinv_tomont _ (Nat.mod_lt _ (by simp [p256]))]

@[step]
theorem multiply_spec (_h : Runs) (pt : mid.p256.AffineMontPoint) (k : mid.p256.Scalar) (P : P256Point)
    (hP : p256OnCurve P) (hrep : p256Represents2 P (pairNat pt.xy.val)) :
    mid.p256.AffineMontPoint.multiply pt k ⦃ q =>
      ∃ rx ry, p256AffineZ (rx, ry) (p256Pow P (wordsNat k.val)) ∧
        pairNat q.xy.val = (2 ^ 256 * rx % p256, 2 ^ 256 * ry % p256) ⦄ := by
  obtain ⟨hX, hY, rfl⟩ := hrep
  have hl : (pt.xy.val).length = 8 := pt.xy.property
  unfold mid.p256.AffineMontPoint.multiply
  step as ⟨fx, hfx⟩
  step as ⟨dx, hdx⟩
  · simpa [feNat, hfx, pairNat] using hX
  step as ⟨fy, hfy⟩
  step as ⟨dy, hdy⟩
  · simpa [feNat, hfy, pairNat_drop _ hl] using hY
  step as ⟨q0, hq0⟩
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
    refine ⟨(pairNat xy1.val).1, (pairNat xy1.val).2, xy1_post _ hP ?_, ?_⟩
    · rw [hq0, pairNat_append _ _ dx.property dy.property, p256Affine]
      simp only [feNat] at hdx hdy
      rw [hdx, hdy, hfx, hfy, Nat.mod_mod, Nat.mod_mod, pairNat_drop _ hl]
      rfl
    · rw [q_post, pairNat_append _ _ fe4.property fe5.property, ← hxa, ← hya]
      exact Prod.ext fe4_post fe5_post

theorem as_bytes_uncompressed_spec (_hr : Runs) (pt : mid.p256.AffineMontPoint) (hx : (pairNat pt.xy.val).1 < p256)
    (hy : (pairNat pt.xy.val).2 < p256) :
    mid.p256.AffineMontPoint.as_bytes_uncompressed pt ⦃ b =>
      b.val.head? = some 4#u8 ∧
        x962Coords b.val = (p256RInv * (pairNat pt.xy.val).1 % p256, p256RInv * (pairNat pt.xy.val).2 % p256) ⦄ := by
  have hl : (pt.xy.val).length = 8 := pt.xy.property
  unfold mid.p256.AffineMontPoint.as_bytes_uncompressed
  simp only [mid.p256.FieldElement.BYTES]
  have h65 : (Array.repeat 65#usize 0#u8).val.length = 65 := by simp [Array.repeat]
  step*
  · have hsl : s.length = 65 := by simp [Slice.length, s_post, Array.repeat]
    rw [indicator_post1, hsl]; simp
  · simpa [feNat, fe_post, pairNat] using hx
  · simp [x_post, s1_post]
  · simpa [feNat, fe2_post, pairNat_drop _ hl] using hy
  · have hsl : s.length = 65 := by simp [Slice.length, s_post, Array.repeat]
    simp [x_post1, indicator_post1, hsl, s2_post]
  · have hsl : s.length = 65 := by simp [Slice.length, s_post, Array.repeat]
    have hxyl : xy.length = 64 := by rw [indicator_post1, hsl]
    have ha32 : (a.val).length = 32 := a.property
    have ha132 : (a1.val).length = 32 := a1.property
    obtain ⟨hxy, hxyl'⟩ := x_post4 x1 y1 (by simp [x1_post, s1_post])
      (by simp [y1_post, s2_post, hxyl])
    obtain ⟨hall, hall'⟩ := indicator_post4 indicator1 (split_at_mut_back1 (x1, y1))
      (by simp [indicator1_post, indicator_post]) (by rw [hxyl', hxyl, hsl])
    have hind : indicator1.val = [4#u8] := by
      rw [indicator1_post, Slice.set_val_eq, indicator_post2, s_post]
      simp [Array.repeat]
    rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by rw [← Slice.length, hall', hsl]; rfl), hall, hind,
      hxy, x1_post, y1_post, s1_post, s2_post, Array.val_to_slice, Array.val_to_slice]
    refine ⟨rfl, ?_⟩
    simp only [x962Coords]
    have h1 : ([4#u8] ++ (a.val ++ a1.val)).slice 1 33 = a.val := by
      simp [List.slice, List.take_left' ha32]
    have h2 : ([4#u8] ++ (a.val ++ a1.val)).slice 33 65 = a1.val := by
      simp [List.slice, List.drop_left' ha32, List.take_of_length_le, ha132]
    rw [h1, h2, a_post, a1_post]
    simp only [feNat] at fe1_post fe3_post
    rw [fe1_post, fe3_post, fe_post, fe2_post, pairNat_drop _ hl]
    rfl

/-- `PrivateKey::vg_diffie_hellman`: pyca/verified-garbage's ECDH of a scalar
below n with a point on the curve. -/
theorem vg_diffie_hellman_spec (h : Runs) (vg : low.x86_64.p256_vg.P256) (k : mid.p256.PrivateKey)
    (peer : mid.p256.PublicKey) (P : P256Point) (hk : wordsNat k.scalar.val < n256)
    (hP : p256OnCurve P) (hrep : p256Represents2 P (pairNat peer.point.xy.val)) :
    mid.p256.PrivateKey.vg_diffie_hellman k vg peer ⦃ r =>
      match p256Pow P (wordsNat k.scalar.val) with
      | some (x, _) => ∃ s, r = .Ok s ∧ beNat s.val = x
      | none => r = .Err .Fault ⦄ := by
  unfold mid.p256.PrivateKey.vg_diffie_hellman mid.p256.Scalar.as_bytes
  obtain ⟨hx, hy, hPe⟩ := hrep
  step with u64x4_to_be_spec k.scalar as ⟨a, ha⟩
  step with as_bytes_uncompressed_spec h peer.point hx hy as ⟨b, hb4, hbc⟩
  have hcb : some (vgP256.coords b.val) = P := by
    rw [← hPe]; exact congrArg some hbc
  step with vg_p256_ecdh_spec vg a b as ⟨o, ho⟩
  simp only [vgBytes, vgP256.ofBytes_bv, ha] at ho
  rw [vgP256.exchange_eq _ hk b.val b.property hb4 (hcb ▸ hP), hcb] at ho
  rcases hq : p256Pow P (wordsNat k.scalar.val) with _ | ⟨x, y⟩ <;> rw [hq] at ho <;> simp only at ho
  · subst ho; simp
  · obtain ⟨out, rfl, hout⟩ := ho
    simp only [WP.spec_ok]
    refine ⟨out, rfl, ?_⟩
    have hon := vgP256.pow_onCurve P hP (wordsNat k.scalar.val)
    rw [hq] at hon
    show beNat out.val = x
    rw [← vgP256.ofBytes_bv, hout,
      vgP256.ofBytes_toBytes_lt _ _ (lt_trans hon.1 (by simp [p256]))]

theorem not_onCurve_zero : ¬ p256OnCurve (some (0, 0)) := by
  simp [p256OnCurve, nist.OnCurve, p256, b256]

@[step]
theorem diffie_hellman_spec (h : Runs) (hvg : RunsP256) (k : mid.p256.PrivateKey) (peer : mid.p256.PublicKey) (P : P256Point)
    (hk : wordsNat k.scalar.val < n256) (hP : p256OnCurve P) (hrep : p256Represents2 P (pairNat peer.point.xy.val)) :
    mid.p256.PrivateKey.diffie_hellman k peer ⦃ r =>
      match p256Pow P (wordsNat k.scalar.val) with
      | some (x, y) =>
        if p256OnCurve (some (x, y)) then ∃ s, r = .Ok s ∧ beNat s.val = x else r = .Err .Fault
      | none => r = .Err .Fault ⦄ := by
  unfold mid.p256.PrivateKey.diffie_hellman low.ct.into_public
  step
  obtain ⟨⟨t, ht⟩, -⟩ := hvg
  simp only [ht, bind_ok]
  rcases t with _ | vg
  swap
  · apply WP.spec_mono (vg_diffie_hellman_spec h vg k peer P hk hP hrep)
    intro r hr
    rcases hq : p256Pow P (wordsNat k.scalar.val) with _ | ⟨x, y⟩ <;> simp only [hq] at hr ⊢
    · exact hr
    · have hon := vgP256.pow_onCurve P hP (wordsNat k.scalar.val)
      rw [hq] at hon
      simp only [hon, ↓reduceIte]
      exact hr
  simp only
  step with multiply_spec h _ _ P hP hrep as ⟨q, rx, ry, hz, hq⟩
  have hl : (q.xy.val).length = 8 := q.xy.property
  step as ⟨b, hb⟩
  rw [hq] at hb
  simp only [rinv_tomont_mod] at hb
  unfold p256AffineZ at hz
  split_ifs at hz with h0
  · obtain ⟨rfl, rfl⟩ := h0
    rw [hz]
    simp only [Nat.zero_mod, not_onCurve_zero, iff_false] at hb
    simp [hb]
  · rw [hz]
    simp only
    by_cases hc : p256OnCurve (some (rx % p256, ry % p256))
    · have hbt : b = true := hb.mpr hc
      simp only [hbt, hc, ↓reduceIte]
      step as ⟨fx, hfx⟩
      have hx := congrArg Prod.fst hq
      simp only [pairNat] at hx
      step as ⟨dx, hdx⟩
      step as ⟨sb, hsb⟩
      refine ⟨sb, rfl, ?_⟩
      simp only [feNat] at hdx
      rw [hsb, hdx, hfx, hx, rinv_tomont_mod]
    · have hbf : b = false := by simpa [hc] using hb
      simp [hbf, hc]

theorem public_from_x962_spec (h : Runs) (bytes : Slice U8) :
    mid.p256.PublicKey.from_x962_uncompressed bytes ⦃ r =>
      match bytes.val.head? with
      | none => r = .Err (.KeyRejected .WrongLength)
      | some b0 =>
        if b0 = 4#u8 then
          if bytes.length = 65 then
            if p256OnCurve (some (x962Coords bytes.val)) then
              ∃ pk, r = .Ok pk ∧ p256Represents2 (some (x962Coords bytes.val)) (pairNat pk.point.xy.val)
            else r = .Err (.KeyRejected .NotOnCurve)
          else r = .Err (.KeyRejected .WrongLength)
        else r = .Err (.KeyRejected .Compressed) ⦄ := by
  unfold mid.p256.PublicKey.from_x962_uncompressed
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
    · by_cases hl : bytes.length = 65 <;> simp only [hl, ↓reduceIte] at hr ⊢
      · by_cases hon : p256OnCurve (some (x962Coords bytes.val)) <;> simp only [hon, ↓reduceIte] at hr ⊢
        · obtain ⟨pt, rfl, hpt⟩ := hr
          simp [hpt]
        · subst hr; simp
      · subst hr; simp
    · subst hr; simp

theorem agree_spec (h : Runs) (hvg : RunsP256) (k : mid.p256.PrivateKey) (hk : wordsNat k.scalar.val < n256)
    (peer : Slice U8) :
    high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.agree k peer ⦃ r =>
      p256Agreement (wordsNat k.scalar.val) peer.val r ⦄ := by
  unfold high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.agree p256Agreement
  step with public_from_x962_spec h peer as ⟨r, hr⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rcases hb : peer.val.head? with _ | b0
  · simp only [hb] at hr
    subst hr
    simp
  · simp only [hb] at hr ⊢
    by_cases h4 : b0 = 4#u8 <;> simp only [h4, ↓reduceIte] at hr ⊢
    · by_cases hl : peer.length = 65 <;> simp only [hl, ↓reduceIte] at hr ⊢
      · by_cases hon : p256OnCurve (some (x962Coords peer.val)) <;> simp only [hon, ↓reduceIte] at hr ⊢
        · obtain ⟨pk, rfl, hpk⟩ := hr
          simp only
          step with diffie_hellman_spec h hvg k pk _ hk hon hpk as ⟨r1, hr1⟩
          rcases hq : p256Pow (some (x962Coords peer.val)) (wordsNat k.scalar.val) with _ | ⟨x, y⟩ <;>
            simp only [hq] at hr1 ⊢
          · subst hr1; simp
          · by_cases hc : p256OnCurve (some (x, y)) <;> simp only [hc, ↓reduceIte] at hr1 ⊢
            · obtain ⟨s, rfl, hs⟩ := hr1
              simp [hs]
            · subst hr1; simp
        · subst hr; simp
      · subst hr; simp
    · subst hr; simp

end P256

open P256

/-! ## The agreement API, `high::agreement`, through the modelled dispatch -/

/-- A P-256 agreement with the peer's encoded public key: `p256Agreement` of
this key's scalar, which `hd` holds below n, as `drawKeygen_ok` proves of a
generated key and `from_bytes_spec` of one loaded from a 32-byte scalar; a
PKCS#8 or SEC 1 load passes other lengths through the same range check,
which no theorem covers yet. Its fault case never happens for a scalar in [1, n) if
every finite point has order n, which `rind.spec.p256_order` proves for every
finite on-curve point, though this theorem does not yet use it to rule the
fault out. -/
theorem p256_agree (h : Runs) (hvg : RunsP256) (key : high.agreement.PrivateKey)
    (k : high.agreement.Keyed high.curve.P256 mid.p256.PrivateKey) (hk : key.«private» = .P256 k)
    (hd : wordsNat k.key.scalar.val < n256) (peer : Slice U8) :
    high.agreement.PrivateKey.agree key peer ⦃ r =>
      p256Agreement (wordsNat k.key.scalar.val) peer.val r ⦄ := by
  unfold high.agreement.PrivateKey.agree high.agreement.Keyed.agree
  rw [hk]
  step with agree_spec h hvg k.key hd peer as ⟨r, hr⟩
  rcases r with s | e <;> simpa using hr

/-- The shared secret's bytes are the ones `p256_agree` states. -/
theorem p256_shared_secret (s : mid.p256.SharedSecret) :
    high.agreement.SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref (.P256 s) ⦃ b =>
      b.val = s.val ⦄ := by
  simp [high.agreement.SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref, Array.val_to_slice]

end rind.x86_64
