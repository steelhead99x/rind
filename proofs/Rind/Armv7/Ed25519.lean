import Rind.Armv7.Curve25519
import Rind.Armv7.Sha512Context
import Rind.DalekEdwards
open Aeneas Aeneas.Std Result rind.spec

/-!
# Ed25519 on armv7, proven from rind's signature API to curve25519-dalek's theorems

On armv7, rind's Ed25519 is `mid::ed25519`'s portable code over
curve25519-dalek's point and scalar arithmetic, whose Beneficial AI
Foundation (BAIF) theorems `Rind.Armv7.Dalek` restates, and SHA-512, which
`Rind.Armv7.Sha512Context` proves down to aws-lc's NEON routine, whose HOL
Light proof `Rind.Armv7.Sha512Entry` restates, on CPUs with NEON, as
`RunsSha512` states. The `ed25519_*` theorems state what the signature API's
`ed25519` module returns, in `Rind.Ed25519`'s terms, as x86_64's and
aarch64's do: `Rind.DalekEdwards` reads BAIF's group of points in those terms.
Above `mid::ed25519` the code is every target's, so those proofs follow
x86_64's.
-/

namespace rind.armv7

/-! ## Bytes -/

@[simp]
theorem length_leBytesOf (k n : Nat) : (leBytesOf k n).length = k := by
  simp [leBytesOf]

theorem leBytesOf_succ (k n : Nat) :
    leBytesOf (k + 1) n = @UScalar.mk UScalarTy.U8 (BitVec.ofNat 8 n) :: leBytesOf k (n / 256) := by
  simp only [leBytesOf, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Bytes are the little-endian bytes of the number they encode. -/
theorem leBytesOf_leNat : ∀ b : List U8, leBytesOf b.length (leNat b) = b
  | [] => rfl
  | x :: xs => by
    have h : leNat (x :: xs) = x.val + 256 * leNat xs := by simp [leNat, Nat.ofDigits_cons]
    have hx : x.val < 256 := x.hBounds
    rw [List.length_cons, leBytesOf_succ, h, show (x.val + 256 * leNat xs) / 256 = leNat xs by omega,
      leBytesOf_leNat xs]
    congr 1
    cases x with
    | mk bv =>
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat] at hx ⊢
      simp only [UScalar.val] at hx ⊢
      omega

/-- The number `k` little-endian bytes encode is the one they were written
from, mod 256ᵏ. -/
theorem leNat_leBytesOf : ∀ k n : Nat, leNat (leBytesOf k n) = n % 256 ^ k
  | 0, n => by simp [leBytesOf, leNat, Nat.mod_one]
  | k + 1, n => by
    rw [leBytesOf_succ]
    simp only [leNat, List.map_cons, Nat.ofDigits_cons]
    rw [show Nat.ofDigits 256 ((leBytesOf k (n / 256)).map (·.val)) = leNat (leBytesOf k (n / 256)) from rfl,
      leNat_leBytesOf k, pow_succ', Nat.mod_mul]
    simp [UScalar.val]

/-- Bytes of one length are equal when the numbers they encode are. -/
theorem leNat_inj (a b : List U8) (hl : a.length = b.length) (h : leNat a = leNat b) : a = b := by
  rw [← leBytesOf_leNat a, ← leBytesOf_leNat b, hl, h]

theorem leNat_lt (b : List U8) : leNat b < 256 ^ b.length := by
  unfold leNat
  have := Nat.ofDigits_lt_base_pow_length (b := 256) (l := b.map (·.val)) (by norm_num)
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact y.hBounds)
  simpa using this

theorem leNat_append (a b : List U8) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  simp [leNat, Nat.ofDigits_append]

theorem leNat_singleton (b : U8) : leNat [b] = b.val := by
  simp [leNat]

theorem setSlice!_at {α : Type _} (X R S : List α) (i : Nat) (hX : X.length = i)
    (h : S.length ≤ R.length) : (X ++ R).setSlice! i S = X ++ S ++ R.drop S.length := by
  simp only [List.setSlice!, ← hX, List.drop_append]
  simp [min_eq_left h]

/-- 32 bytes are their first 31 and their last. -/
theorem split_last31 (l : List U8) (hl : l.length = 32) :
    ∃ t b, t.length = 31 ∧ l = t ++ [b] := by
  refine ⟨l.dropLast, l.getLast (by rintro rfl; simp at hl), by simp [hl], ?_⟩
  exact (List.dropLast_append_getLast _).symm

/-- Of two byte strings of one length that agree above byte `i` and differ
there, the one smaller at `i` encodes the smaller number. -/
theorem leNat_lt_of_top (y q : List U8) (hl : y.length = q.length) (i : Nat) (hi : i < y.length)
    (htop : y.drop (i + 1) = q.drop (i + 1)) (hlt : (y[i]'hi).val < (q[i]'(hl ▸ hi)).val) :
    leNat y < leNat q := by
  have hy : y = y.take i ++ [y[i]'hi] ++ y.drop (i + 1) := by simp
  have hq : q = q.take i ++ [q[i]'(hl ▸ hi)] ++ q.drop (i + 1) := by simp
  have hyl : (y.take i).length = i := by simp; omega
  have hql : (q.take i).length = i := by simp; omega
  rw [hy, hq, leNat_append, leNat_append, leNat_append, leNat_append, leNat_singleton, leNat_singleton,
    List.length_append, List.length_append, hyl, hql, htop]
  have h1 := leNat_lt (y.take i)
  rw [hyl] at h1
  simp only [List.length_singleton]
  have h2 : 256 ^ i * (y[i]'hi).val + 256 ^ i ≤ 256 ^ i * (q[i]'(hl ▸ hi)).val := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hlt
  have h3 := Nat.zero_le (leNat (q.take i))
  rw [pow_succ]
  nlinarith

/-! ## Hashing, `mid::ed25519::ed25519_digest` -/

theorem context_new_spec : mid.sha2.Sha512Context.new ⦃ c => Hashed sha512Iv c [] ⦄ := by
  unfold mid.sha2.Sha512Context.new
  step with sha512_initial_spec as ⟨st, hh, hn⟩
  exact resume_spec _ st hh hn

@[step]
theorem ed25519_digest_spec (h : RunsSha512) (x1 x2 x3 : Slice U8)
    (hl : x1.length + x2.length + x3.length < 2 ^ 64) :
    mid.ed25519.ed25519_digest x1 x2 x3 ⦃ d => d.val = sha512 (x1.val ++ x2.val ++ x3.val) ⦄ := by
  unfold mid.ed25519.ed25519_digest
  simp only [Slice.length] at hl
  step with context_new_spec as ⟨c, hc⟩
  step with context_update_spec h _ c [] x1 hc (by simp [Slice.length]; omega) as ⟨c1, hc1⟩
  step with context_update_spec h _ c1 _ x2 hc1 (by simp [Slice.length]; omega) as ⟨c2, hc2⟩
  step with context_update_spec h _ c2 _ x3 hc2 (by simp [Slice.length]; omega) as ⟨c3, hc3⟩
  step with context_finish_spec h _ c3 _ hc3 as ⟨d, hd⟩
  simpa [sha512] using hd

/-! ## Slices and arrays -/

/-- `<&[T; N]>::try_from(&[T])`, which Aeneas's library gives no spec. -/
theorem try_from_shared_spec {T : Type} (N : Usize) (s : Slice T) :
    core.array.TryFromSharedArraySlice.try_from N s ⦃ r =>
      if s.length = N.val then ∃ a, r = .Ok a ∧ a.val = s.val else ∃ e, r = .Err e ⦄ := by
  unfold core.array.TryFromSharedArraySlice.try_from
  have hl : s.len = N ↔ s.length = N.val := by
    rw [← Slice.len_val]
    exact ⟨fun h => by rw [h], fun h => UScalar.eq_of_val_eq h⟩
  by_cases h : s.len = N
  · simp [h, hl.mp h]
  · simp [h, mt hl.mpr h]

/-- `<[T; N]>::try_from(&[T])` of a slice of `N` elements. -/
@[step]
theorem try_from_copy_ok {T : Type} (N : Usize) (inst : core.marker.Copy T) (s : Slice T)
    (h : s.length = N.val) :
    core.array.TryFromArrayCopySlice.try_from N inst s ⦃ r => ∃ a, r = .Ok a ∧ a.val = s.val ⦄ := by
  apply WP.spec_mono (core.array.TryFromArrayCopySlice.try_from.step N inst s)
  rintro (a | e) hr
  · exact ⟨a, rfl, hr.1⟩
  · exact absurd h hr

/-- `&[u8] == [u8; N]`. -/
@[step]
theorem slice_eq_array_spec {N : Usize} (s : Slice U8) (a : Std.Array U8 N) :
    Shared0Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8 s a ⦃ b => b ↔ s.val = a.val ⦄ := by
  unfold Shared0Slice.Insts.CoreCmpPartialEqArray.eq
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ s a.to_slice
    (fun x y => by simp [liftFun2]))
  intro b hb
  rw [hb, Slice.eq_iff, Array.val_to_slice]

/-- `[u8] == [u8]`. -/
@[step]
theorem slice_eq_spec (s t : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s t ⦃ b => b ↔ s.val = t.val ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ s t
    (fun x y => by simp [liftFun2]))
  intro b hb
  rw [hb, Slice.eq_iff]

/-- `[u8; N] == [u8; N]`. -/
@[step]
theorem array_eq_spec {N : Usize} (a b : Std.Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ r => r ↔ a.val = b.val ⦄ := by
  have he : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b =
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a.to_slice b.to_slice := by
    unfold core.array.equality.PartialEqArray.eq core.slice.cmp.PartialEqSlice.eq
    simp [Slice.length, Array.length]
  rw [he]
  apply WP.spec_mono (slice_eq_spec a.to_slice b.to_slice)
  intro r hr
  simpa using hr

/-! ## dalek's points and scalars, read in `Rind.Ed25519`'s terms -/

/-- A dalek point BAIF's theorems take, representing `A`. -/
def Holds (P : curve25519_dalek.edwards.EdwardsPoint) (A : EdPoint) : Prop :=
  P.Valid ∧ ofDalek P.toPoint = A

/-- Bytes that dalek encodes a point to are its encoding's, in
`Rind.Ed25519`'s terms. -/
theorem encode_val (c : Std.Array U8 32#usize) (P : curve25519.edwards.Point)
    (hc : c.toVector = curve25519.encode P) : c.val = leBytesOf 32 (edEncode (ofDalek P)) := by
  have hl : leNat c.val = edEncode (ofDalek P) := by
    rw [← decodeLittleEndian_toVector, hc, decodeLittleEndian_encode, ← edEncode_ofDalek]
  have := leBytesOf_leNat c.val
  rw [c.property, hl] at this
  exact this.symm

/-- The bytes `compress` writes for a point are its encoding's. -/
theorem compress_bytes_spec (P : curve25519_dalek.edwards.EdwardsPoint) (A : EdPoint) (hP : Holds P A) :
    curve25519_dalek.edwards.EdwardsPoint.compress P ⦃ c => c.val = leBytesOf 32 (edEncode A) ⦄ := by
  apply WP.spec_mono (dalek_compress_spec P hP.1)
  intro c hc
  rw [encode_val c _ hc, hP.2]

theorem L_pos : 0 < curve25519.L := by
  rw [L_eq]
  norm_num [n25519]

theorem L_lt : curve25519.L < 2 ^ 255 := by
  rw [L_eq]
  norm_num [n25519]

/-! ## Clamping, `curve25519_dalek::scalar::clamp_integer` -/

theorem and_248 (x : U8) : (x &&& 248#u8).val = x.val / 8 * 8 := by
  have hx : x.val < 256 := x.hBounds
  rw [UScalar.val_and]
  have : ∀ v < 256, v &&& 248 = v / 8 * 8 := by decide
  exact this _ hx

theorem and_127_or_64 (x : U8) : ((x &&& 127#u8) ||| 64#u8).val = x.val % 64 + 64 := by
  have hx : x.val < 256 := x.hBounds
  rw [UScalar.val_or, UScalar.val_and]
  have : ∀ v < 256, v &&& 127 ||| 64 = v % 64 + 64 := by decide
  exact this _ hx

theorem and_127 (x : U8) : (x &&& 127#u8).val = x.val % 128 := by
  have hx : x.val < 256 := x.hBounds
  rw [UScalar.val_and]
  have : ∀ v < 256, v &&& 127 = v % 128 := by decide
  exact this _ hx

theorem leNat_cons (x : U8) (l : List U8) : leNat (x :: l) = x.val + 256 * leNat l := by
  simp [leNat, Nat.ofDigits_cons]

/-- `clamp_integer` is RFC 8032's pruning of the scalar its bytes encode. -/
@[step]
theorem clamp_integer_spec (a : Std.Array U8 32#usize) :
    curve25519_dalek.scalar.clamp_integer a ⦃ r => leNat r.val = edClamp (leNat a.val) ⦄ := by
  have hl : a.val.length = 32 := a.property
  obtain ⟨t, b31, ht, hab⟩ := split_last31 a.val hl
  obtain ⟨b0, m, rfl⟩ : ∃ b0 m, t = b0 :: m := by
    cases t with
    | nil => simp at ht
    | cons b0 m => exact ⟨b0, m, rfl⟩
  have hm : m.length = 30 := by simpa using ht
  unfold curve25519_dalek.scalar.clamp_integer
  step*
  have hi : i = b0 := by simp_all
  have hi2 : i2 = b31 := by simp_all
  have hi4 : i4 = i3 := by simp_all
  have hr : r.val = i1 :: m ++ [i5] := by simp_all [List.set_append_right]
  have hv1 : i1.val = b0.val / 8 * 8 := by
    rw [i1_post, hi]
    have : ∀ v < 256, v &&& 248 = v / 8 * 8 := by decide
    exact this _ b0.hBounds
  have hv5 : i5.val = b31.val % 64 + 64 := by
    rw [i5_post, hi4, UScalar.val_or, i3_post, UScalar.val_and, hi2]
    have : ∀ v < 256, v &&& 127 ||| 64 = v % 64 + 64 := by decide
    exact this _ b31.hBounds
  rw [hr, hab, List.cons_append, List.cons_append, leNat_cons, leNat_cons, leNat_append, leNat_append,
    leNat_singleton, leNat_singleton, hm, hv1, hv5]
  have hM := leNat_lt m
  rw [hm] at hM
  have h0 : b0.val < 256 := b0.hBounds
  have h31 : b31.val < 256 := b31.hBounds
  unfold edClamp
  omega

/-! ## Decoding, `mid::edwards25519::Point::from_bytes` -/

theorem leNat_ONE : leNat (leBytesOf 32 1) = 1 := by
  rw [leNat_leBytesOf]
  exact Nat.mod_eq_of_lt (by norm_num)

theorem leNat_P_MINUS_ONE : leNat (leBytesOf 32 (p25519 - 1)) = p25519 - 1 := by
  rw [leNat_leBytesOf]
  norm_num [p25519]

@[step]
theorem ONE_spec : mid.edwards25519.ONE ⦃ a => a.val = leBytesOf 32 1 ⦄ := by
  unfold mid.edwards25519.ONE
  step*
  simp_all [Std.Array.repeat]
  decide

@[step]
theorem P_MINUS_ONE_spec : mid.edwards25519.P_MINUS_ONE ⦃ a => a.val = leBytesOf 32 (p25519 - 1) ⦄ := by
  unfold mid.edwards25519.P_MINUS_ONE
  step*
  simp_all [Std.Array.repeat]
  decide

theorem is_below_p_loop_spec (y : Std.Array U8 32#usize) (i : Usize) (hi : i.val ≤ 32)
    (htop : y.val.drop i.val = (leBytesOf 32 (p25519 - 1)).drop i.val) :
    mid.edwards25519.is_below_p_loop y i ⦃ b => b = decide (leNat y.val < p25519) ⦄ := by
  have hyl : y.val.length = 32 := y.property
  have hp : leNat (leBytesOf 32 (p25519 - 1)) = p25519 - 1 := leNat_P_MINUS_ONE
  have hp0 : 0 < p25519 := by norm_num [p25519]
  have hq : (leBytesOf 32 (p25519 - 1)).length = 32 := by simp
  unfold mid.edwards25519.is_below_p_loop
  apply loop.spec_decr_nat (fun j : Usize => j.val)
    (fun j => j.val ≤ 32 ∧ y.val.drop j.val = (leBytesOf 32 (p25519 - 1)).drop j.val)
  · rintro j ⟨hj, hjt⟩
    unfold mid.edwards25519.is_below_p_loop.body
    split
    · rename_i hpos
      step as ⟨i1, hi1⟩
      have hk : i1.val < 32 := by scalar_tac
      step as ⟨i2, hi2⟩
      step with P_MINUS_ONE_spec as ⟨a, ha⟩
      step as ⟨i3, hi3⟩
      have hyi : i2 = y.val[i1.val]'(by omega) := by simp_all
      have hai : i3 = (leBytesOf 32 (p25519 - 1))[i1.val]'(by omega) := by simp_all
      have htop' : y.val.drop (i1.val + 1) = (leBytesOf 32 (p25519 - 1)).drop (i1.val + 1) := by
        rw [show i1.val + 1 = j.val by scalar_tac]
        exact hjt
      split
      · rename_i hne
        step as ⟨i4, hi4⟩
        have hai4 : i4 = i3 := by simp_all
        subst hai4
        have hv : i2.val ≠ i4.val := fun h => by simp_all [UScalar.eq_of_val_eq h]
        rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
        · have := leNat_lt_of_top y.val _ (by rw [hyl, hq]) i1.val (by omega) htop'
            (by rw [← hyi, ← hai]; exact hlt)
          have hb : leNat y.val < p25519 := by omega
          exact decide_eq_decide.mpr ⟨fun _ => hb, fun _ => hlt⟩
        · have := leNat_lt_of_top _ y.val (by rw [hyl, hq]) i1.val (by omega) htop'.symm
            (by rw [← hyi, ← hai]; exact hgt)
          have hb : ¬ leNat y.val < p25519 := by omega
          exact decide_eq_decide.mpr ⟨fun h => absurd (show i2.val < i4.val from h) (by omega),
            fun h => absurd h hb⟩
      · rename_i heq
        simp only [WP.spec_ok]
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hii : i2 = i3 := UScalar.eq_of_val_eq (by simpa using heq)
        rw [List.drop_eq_getElem_cons (by omega : i1.val < y.val.length),
          List.drop_eq_getElem_cons (by omega : i1.val < (leBytesOf 32 (p25519 - 1)).length), htop', ← hyi,
          ← hai, hii]
    · rename_i hz
      have hj0 : j.val = 0 := by scalar_tac
      rw [hj0, List.drop_zero, List.drop_zero] at hjt
      simp [hjt, hp, hp0]
  · exact ⟨hi, htop⟩

/-- `is_below_p` is whether the 32 bytes encode a number below p. -/
@[step]
theorem is_below_p_spec (y : Std.Array U8 32#usize) :
    mid.edwards25519.is_below_p y ⦃ b => b = decide (leNat y.val < p25519) ⦄ := by
  unfold mid.edwards25519.is_below_p
  step*
  apply is_below_p_loop_spec y _ (by simp_all)
  simp_all [List.drop_of_length_le]

open Classical in
/-- What dalek's `decompress` returns for an encoding of y below p, other
than one of x = 0 with the sign bit set, is `edDecode`'s point. -/
theorem decompress_post (bytes : Std.Array U8 32#usize) (o : Option curve25519_dalek.edwards.EdwardsPoint)
    (hmap : o.map (·.toPoint) = curve25519.decodeLenient bytes.toVector)
    (hvalid : ∀ P, o = some P → P.Valid)
    (hy : leNat bytes.val % 2 ^ 255 < p25519)
    (hs : ¬((leNat bytes.val % 2 ^ 255 = 1 ∨ leNat bytes.val % 2 ^ 255 = p25519 - 1) ∧
      leNat bytes.val / 2 ^ 255 = 1)) :
    if edValidEncode (leNat bytes.val) then ∃ P, o = some P ∧ Holds P (edDecode (leNat bytes.val))
    else o = none := by
  have hn : leNat bytes.val < 2 ^ 256 := by
    have := leNat_lt bytes.val
    rwa [bytes.property] at this
  obtain ⟨hsome, hnone⟩ := decodeLenientNat_canonical _ hn hy hs
  rw [curve25519.decodeLenient, decodeLittleEndian_toVector] at hmap
  cases o with
  | none =>
    have := hnone (by simpa using hmap.symm)
    simp [this]
  | some P =>
    obtain ⟨hv, hd⟩ := hsome P.toPoint (by simpa using hmap.symm)
    simp only [hv, ite_true]
    exact ⟨P, rfl, hvalid P rfl, hd.symm⟩

theorem map_constructor (o : Option curve25519_dalek.edwards.EdwardsPoint) :
    core.option.Option.map P.Insts.CoreOpsFunctionFnOnceTupleEdwardsPointPoint o
      mid.edwards25519.Point.constructor = ok o := by
  cases o <;> simp [core.option.Option.map, P.Insts.CoreOpsFunctionFnOnceTupleEdwardsPointPoint.call_once, mid.edwards25519.Point.constructor]

open Classical in
/-- `Point::from_bytes` decodes exactly the encodings of points of the group,
as `edDecode` does. -/
@[step]
theorem point_from_bytes_spec (bytes : Std.Array U8 32#usize) :
    mid.edwards25519.Point.from_bytes bytes ⦃ o =>
      if edValidEncode (leNat bytes.val) then ∃ P, o = some P ∧ Holds P (edDecode (leNat bytes.val))
      else o = none ⦄ := by
  have hbl : bytes.val.length = 32 := bytes.property
  obtain ⟨t, b31, ht, hab⟩ := split_last31 bytes.val hbl
  have htl := leNat_lt t
  rw [ht] at htl
  have h31 : b31.val < 256 := b31.hBounds
  have hn : leNat bytes.val = leNat t + 256 ^ 31 * b31.val := by
    rw [hab, leNat_append, leNat_singleton, ht]
  -- The bytes with the sign bit cleared, as `y`.
  have hy : ∀ c : U8, c = b31 &&& 127#u8 →
      leNat (bytes.val.set 31 c) = leNat bytes.val % 2 ^ 255 := by
    intro c hc
    rw [hn, hab, List.set_append_right _ _ (by omega), ht, Nat.sub_self, List.set_cons_zero]
    simp only [leNat_append, leNat_singleton, ht, hc, and_127]
    omega
  unfold mid.edwards25519.Point.from_bytes
  simp only [map_constructor]
  step*
  have hb : i = b31 := by rw [i_post]; simp [hab, ht]
  have hi1 : i1 = b31 &&& 127#u8 := by rw [← hb]; exact UScalar.eq_of_val_eq i1_post
  have hsv : i2.val = leNat bytes.val / 2 ^ 255 := by
    rw [i2_post, hb, Nat.shiftRight_eq_div_pow, hn]
    omega
  subst index_mut_back_post hi1
  have hYn : leNat (bytes.set 31#usize (b31 &&& 127#u8)).val = leNat bytes.val % 2 ^ 255 := by
    rw [Std.Array.set_val_eq]
    exact hy _ rfl
  have hYl : (bytes.set 31#usize (b31 &&& 127#u8)).val.length = 32 := (bytes.set _ _).property
  -- A leaf returning `none` is right when the bytes are no point's encoding.
  have hnone : ¬edValidEncode (leNat bytes.val) →
      if edValidEncode (leNat bytes.val) then ∃ P, (none : Option mid.edwards25519.Point) = some P ∧
        Holds P (edDecode (leNat bytes.val)) else True := fun h => by simp [h]
  split
  · rename_i hs1
    have hs : leNat bytes.val / 2 ^ 255 = 1 := by rw [← hsv, hs1]; rfl
    step with ONE_spec as ⟨one, hone⟩
    step with array_eq_spec as ⟨e1, he1⟩
    split
    · rename_i he
      have h1 : leNat bytes.val % 2 ^ 255 = 1 := by rw [← hYn, he1.mp he, hone, leNat_ONE]
      step*
      all_goals exact hnone fun hv => (edValidEncode_canonical hv).2.2 ⟨Or.inl h1, hs⟩
    · rename_i he
      have h1 : leNat bytes.val % 2 ^ 255 ≠ 1 := fun h =>
        he (he1.mpr (leNat_inj _ _ (by rw [hYl, hone, length_leBytesOf]) (by rw [hYn, hone, leNat_ONE, h])))
      step with P_MINUS_ONE_spec as ⟨pm, hpm⟩
      step with array_eq_spec as ⟨e2, he2⟩
      step with is_below_p_spec as ⟨b, hbp⟩
      split
      · rename_i hb
        have hylt : leNat bytes.val % 2 ^ 255 < p25519 := by
          rw [← hYn]
          exact of_decide_eq_true (hbp ▸ hb)
        split
        · rename_i he'
          have hp : leNat bytes.val % 2 ^ 255 = p25519 - 1 := by
            rw [← hYn, he2.mp he', hpm, leNat_P_MINUS_ONE]
          rw [WP.spec_ok, ite_eq_right fun hv => (edValidEncode_canonical hv).2.2 ⟨Or.inr hp, hs⟩]
        · rename_i he'
          have hp : leNat bytes.val % 2 ^ 255 ≠ p25519 - 1 := fun h =>
            he' (he2.mpr (leNat_inj _ _ (by rw [hYl, hpm, length_leBytesOf])
              (by rw [hYn, hpm, leNat_P_MINUS_ONE, h])))
          step with dalek_decompress_spec as ⟨o, hmap, hvalid⟩
          exact decompress_post bytes o hmap hvalid hylt (by omega)
      · rename_i hb
        have hnv : ¬edValidEncode (leNat bytes.val) := fun hv => hb (by
          rw [hbp, hYn]
          simpa using (edValidEncode_canonical hv).2.1)
        rw [WP.spec_ok, ite_eq_right hnv]
  · rename_i hs1
    have hs : leNat bytes.val / 2 ^ 255 ≠ 1 := fun h => hs1 (UScalar.eq_of_val_eq (by rw [hsv, h]; rfl))
    step*
    · have hylt : leNat bytes.val % 2 ^ 255 < p25519 := by
        rw [← hYn]
        exact of_decide_eq_true (b_post ▸ ‹b = true›)
      exact decompress_post bytes o o_post o_post1 hylt (by omega)
    · refine hnone fun hv => ‹¬b = true› ?_
      rw [b_post, hYn]
      simpa using (edValidEncode_canonical hv).2.1

/-! ## Verifying keys, `mid::ed25519::VerifyingKey` -/

/-- A verifying key whose dalek point BAIF's theorems take, representing `P`. -/
def HoldsPoint (vk : mid.ed25519.VerifyingKey) (P : EdPoint) : Prop := Holds vk.point P

open Classical in
theorem mid_from_bytes_spec (hs : RunsSha512) (bytes : Slice U8) :
    mid.ed25519.VerifyingKey.from_bytes bytes ⦃ r =>
      if bytes.length = 32 then
        if edValidEncode (leNat bytes.val) then
          ∃ vk, r = .Ok vk ∧ vk.bytes.val = bytes.val ∧ HoldsPoint vk (edDecode (leNat bytes.val))
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold mid.ed25519.VerifyingKey.from_bytes
  step with assert_held_spec hs
  step with core.array.TryFromArrayCopySlice.try_from.step 32#usize core.marker.CopyU8 bytes as ⟨r, hr⟩
  by_cases hl : bytes.length = 32
  · simp only [hl, ↓reduceIte]
    rcases r with a | e
    · obtain ⟨ha, -⟩ := hr
      simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with point_from_bytes_spec a as ⟨o, ho⟩
      rw [ha] at ho
      split_ifs at ho ⊢ with hv
      · obtain ⟨P, rfl, hP⟩ := ho
        simp [core.option.Option.ok_or, HoldsPoint, ha, hP]
      · subst ho
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromKeyFormatError.from]
    · exact absurd hl hr
  · simp only [hl, ↓reduceIte]
    rcases r with a | e
    · have := a.property
      exact absurd (by simp_all [Slice.length]) hl
    · simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
        mid.ed25519.VerifyingKey.from_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyFormatError.call_once,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromKeyFormatError.from]

/-! ## Small-order keys, `high::ed25519::has_small_order` -/

@[step]
theorem has_small_order_loop_spec (y : Std.Array U64 4#usize)
    (it : core.slice.iter.Iter (Std.Array U64 4#usize)) (found : Bool) :
    high.ed25519.has_small_order_loop it y found ⦃ b =>
      b = (found || (it.slice.val.drop it.i).any fun c => decide (wordsNat y.val = wordsNat c.val)) ⦄ := by
  unfold high.ed25519.has_small_order_loop
  apply loop.spec_decr_nat (fun x => x.1.slice.val.length - x.1.i)
    (fun x => x.1.slice = it.slice ∧
      (x.2 || (x.1.slice.val.drop x.1.i).any fun c => decide (wordsNat y.val = wordsNat c.val)) =
      (found || (it.slice.val.drop it.i).any fun c => decide (wordsNat y.val = wordsNat c.val)))
  · rintro ⟨it', f⟩ ⟨hsl, hinv⟩
    simp only at hsl hinv ⊢
    unfold high.ed25519.has_small_order_loop.body
    simp only [core.slice.iter.IteratorSliceIter.next]
    split
    · rename_i hlt
      have hlt' : it'.i < it'.slice.val.length := by simpa [Slice.len] using hlt
      step*
      refine ⟨hsl, ?_, by omega⟩
      rw [← hinv, List.drop_eq_getElem_cons hlt', List.any_cons, b_post, s_post, s1_post,
        Array.val_to_slice, Array.val_to_slice, Bool.or_assoc]
      rfl
    · rename_i hge
      have hge' : it'.slice.val.length ≤ it'.i := by simpa [Slice.len] using hge
      rw [← hinv, List.drop_eq_nil_of_le hge']
      simp
  · exact ⟨rfl, rfl⟩

@[step]
theorem small_order_y_spec :
    high.ed25519.has_small_order.SMALL_ORDER_Y ⦃ t => t.val.map (fun c => wordsNat c.val) = edSmallOrderY ⦄ := by
  unfold high.ed25519.has_small_order.SMALL_ORDER_Y high.ed25519.has_small_order.near_p
  step*
  simp_all [Std.Array.make, Std.Array.repeat, wordsNat, Nat.ofDigits, edSmallOrderY, p25519, U64.rMax]

theorem any_eq_mem (l : List (Std.Array U64 4#usize)) (Y : Nat) :
    (l.any fun c => decide (Y = wordsNat c.val)) = decide (Y ∈ l.map fun c => wordsNat c.val) := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

/-- `has_small_order` refuses the 32-byte encodings whose y-coordinate, the
low 255 bits, is in libsodium's list. -/
@[step]
theorem has_small_order_spec (bytes : Slice U8) :
    high.ed25519.has_small_order bytes ⦃ b =>
      b = decide (bytes.length = 32 ∧ leNat bytes.val % 2 ^ 255 ∈ edSmallOrderY) ⦄ := by
  unfold high.ed25519.has_small_order
  step with le_slice_to_u64x4_spec bytes as ⟨o, ho⟩
  split_ifs at ho with hl
  · obtain ⟨y, rfl, hy⟩ := ho
    simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
    step*
    have hi : i.val = 2 ^ 63 - 1 := by rw [i_post]; decide
    have hi2 : i2.val = i1.val % 2 ^ 63 := by
      rw [i2_post, UScalar.val_and, hi, Nat.and_two_pow_sub_one_eq_mod]
    have hl4 : y.val.length = 4 := y.property
    obtain ⟨l, hl'⟩ : ∃ l, y.val = l := ⟨_, rfl⟩
    rcases l with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp [hl'] at hl4
    have ha : wordsNat a.val = leNat bytes.val % 2 ^ 255 := by
      rw [← hy, a_post]
      simp [i1_post, hl'] at hi2
      simp [Std.Array.set_val_eq, hl', wordsNat, Nat.ofDigits, hi2]
      have h0 : w0.val < 2 ^ 64 := w0.hBounds
      have h1 : w1.val < 2 ^ 64 := w1.hBounds
      have h2 : w2.val < 2 ^ 64 := w2.hBounds
      have h3 : w3.val < 2 ^ 64 := w3.hBounds
      omega
    rw [b_post, List.drop_zero, Slice.from_val, Bool.false_or, ← ha, ← «rind.spec.edSmallOrderY_post»,
      any_eq_mem]
    simp [hl]
  · subst ho
    simp [hl]

open Classical in
/-- `high_from_bytes_spec` for whatever `mid::ed25519::VerifyingKey::from_bytes`
holds of the key it loads, `Q`. -/
theorem high_from_bytes_of (h : Runs) (Q : mid.ed25519.VerifyingKey → Prop) (bytes : Slice U8)
    (hmid : mid.ed25519.VerifyingKey.from_bytes bytes ⦃ r =>
      if bytes.length = 32 then
        if edValidEncode (leNat bytes.val) then ∃ vk, r = .Ok vk ∧ vk.bytes.val = bytes.val ∧ Q vk
        else r = .Err (.KeyRejected .NotOnCurve)
      else r = .Err (.KeyRejected .WrongLength) ⦄) :
    high.ed25519.Ed25519VerifyingKey.from_bytes bytes ⦃ r =>
      if bytes.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if leNat bytes.val % 2 ^ 255 ∈ edSmallOrderY then r = .Err (.KeyRejected .SmallOrder)
      else if edValidEncode (leNat bytes.val) then
        ∃ vk, r = .Ok vk ∧ (mid.ed25519.VerifyingKey.bytes vk).val = bytes.val ∧ Q vk
      else r = .Err (.KeyRejected .NotOnCurve) ⦄ := by
  unfold high.ed25519.Ed25519VerifyingKey.from_bytes
  step with new_public_spec h
  step as ⟨b, hb⟩
  by_cases hl : bytes.length = 32
  · by_cases hso : leNat bytes.val % 2 ^ 255 ∈ edSmallOrderY
    · simp only [hb, hl, hso, and_self, decide_true, ↓reduceIte, ne_eq, not_true_eq_false]
      simp [error.Error.Insts.CoreConvertFromKeyFormatError.from]
    · simp only [hb, hl, hso, and_false, decide_false, Bool.false_eq_true, ↓reduceIte, ne_eq,
        not_true_eq_false]
      step with hmid as ⟨r, hr⟩
      simp only [hl, ↓reduceIte] at hr
      split_ifs at hr ⊢ with hv
      · obtain ⟨vk, rfl, hvb, hvp⟩ := hr
        simp [core.result.Result.map, P.Insts.CoreOpsFunctionFnOnceTupleVerifyingKeyEd25519VerifyingKey.call_once,
          high.ed25519.Ed25519VerifyingKey.constructor, hvb, hvp]
      · subst hr
        simp [core.result.Result.map]
  · simp only [hb, hl, false_and, decide_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_false_eq_true]
    step with hmid as ⟨r, hr⟩
    simp only [hl, ↓reduceIte] at hr
    subst hr
    simp [core.result.Result.map]

open Classical in
theorem high_from_bytes_spec (h : Runs) (hs : RunsSha512) (bytes : Slice U8) :
    high.ed25519.Ed25519VerifyingKey.from_bytes bytes ⦃ r =>
      if bytes.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if leNat bytes.val % 2 ^ 255 ∈ edSmallOrderY then r = .Err (.KeyRejected .SmallOrder)
      else if edValidEncode (leNat bytes.val) then
        ∃ vk, r = .Ok vk ∧ (mid.ed25519.VerifyingKey.bytes vk).val = bytes.val ∧
          HoldsPoint vk (edDecode (leNat bytes.val))
      else r = .Err (.KeyRejected .NotOnCurve) ⦄ :=
  high_from_bytes_of h (fun vk => HoldsPoint vk (edDecode (leNat bytes.val))) bytes (mid_from_bytes_spec hs bytes)

/-! ## Verification, `mid::ed25519::VerifyingKey::verify` -/

/-- subtle's `CtOption` to `Option`: its value if its flag is 1. -/
@[step]
theorem from_ct_option_spec {T : Type} (c : subtle.CtOption T) :
    core.option.Option.Insts.CoreConvertFromCtOption.from c ⦃ o =>
      o = if c.is_some = 1#u8 then some c.value else none ⦄ := by
  unfold core.option.Option.Insts.CoreConvertFromCtOption.from subtle.CtOption.impl.is_some
    subtle.Choice.unwrap_u8
  by_cases h : c.is_some = 1#u8 <;> simp [h]

open Classical in
/-- `verify` with a key whose dalek point represents `A`, and whose bytes are
`vk.bytes`: RFC 8032's verification. -/
theorem mid_verify_spec (hs : RunsSha512) (vk : mid.ed25519.VerifyingKey) (A : EdPoint)
    (hp : HoldsPoint vk A) (sig : Std.Array U8 64#usize) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    mid.ed25519.VerifyingKey.verify vk sig msg ⦃ r =>
      r = if ed25519Verifies A vk.bytes.val msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  obtain ⟨hPv, hPA⟩ := hp
  have hsig : sig.val.length = 64 := sig.property
  have hL0 := L_pos
  have hn255 : n25519 < 2 ^ 255 := by have := L_lt; rwa [L_eq] at this
  unfold mid.ed25519.VerifyingKey.verify
  step*
  have hs2 : s2.val = sig.val.drop 32 := by simp_all [Array.val_to_slice]
  have hr : sig_r.val = sig.val.take 32 := by simp_all [Array.val_to_slice]
  have hS2 : Array.asNat 8 s2 = leNat (sig.val.drop 32) := by rw [asNat_eq_leNat, hs2]
  by_cases hS : leNat (sig.val.drop 32) < n25519
  · have h1 : co.is_some = 1#u8 := co_post (by rw [hS2, L_eq]; exact hS)
    simp only [o_post, h1, ↓reduceIte, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_ok]
    have hlr : sig_r.val.length = 32 := by simpa [Slice.length] using sig_r_post
    step as ⟨s3, hs3⟩
    have hl3 : s3.val.length = 32 := by rw [hs3, Array.val_to_slice]; exact vk.bytes.property
    step with ed25519_digest_spec hs sig_r s3 msg (by simp only [Slice.length] at hm ⊢; omega) as ⟨d, hd⟩
    step with dalek_from_bytes_mod_order_wide_spec d as ⟨k, hk⟩
    step with dalek_neg_spec vk.point hPv as ⟨ep, hepv, hep⟩
    have hkL : k.bytes.asNat 8 < curve25519.L := by rw [hk]; exact Nat.mod_lt _ hL0
    have hSv : co.value.bytes.asNat 8 = leNat (sig.val.drop 32) := by rw [s2_post, hS2]
    step with dalek_vartime_double_scalar_mul_basepoint_spec k ep co.value (lt_trans hkL L_lt) hepv
      (by rw [hSv]; omega) as ⟨r2, hr2v, hr2⟩
    step with compress_bytes_spec r2 _ ⟨hr2v, rfl⟩ as ⟨cey, hcey⟩
    step with slice_eq_array_spec sig_r cey as ⟨b, hb⟩
    -- The point `verify` recomputes is RFC 8032's.
    have hX : ofDalek r2.toPoint = edMul (edPow (edNeg A)
        (leNat (sha512 (sig_r.val ++ vk.bytes.val ++ msg.val)) % n25519))
        (edPow edB (leNat (sig.val.drop 32))) := by
      rw [hr2, ofDalek_add, ofDalek_nsmul, ofDalek_nsmul, hep, ofDalek_neg, hPA, ofDalek_basepoint, hk, hSv,
        asNat_eq_leNat, hd, hs3, Array.val_to_slice, L_eq]
    have hlt : edEncode (ofDalek r2.toPoint) < 256 ^ 32 := by
      rw [edEncode_ofDalek]
      exact curve25519.encodeNat_lt_two_pow_256 _
    have hiff : sig_r.val = cey.val ↔ ed25519Verifies A vk.bytes.val msg.val sig.val := by
      rw [ed25519Verifies, ← hr, ← hX, hcey]
      constructor
      · intro he
        refine ⟨hsig, hS, ?_⟩
        rw [he, leNat_leBytesOf, Nat.mod_eq_of_lt hlt]
      · rintro ⟨-, -, he⟩
        exact leNat_inj _ _ (by simp [hlr]) (by rw [he, leNat_leBytesOf, Nat.mod_eq_of_lt hlt])
    by_cases hv : ed25519Verifies A vk.bytes.val msg.val sig.val
    · simp [hb.mpr (hiff.mpr hv), hv]
    · have : b = false := by simpa [hiff, hv] using hb
      simp [this, hv]
  · have h0 : co.is_some = 0#u8 := co_post1 (by rw [hS2, L_eq]; omega)
    have hn : ¬ ed25519Verifies A vk.bytes.val msg.val sig.val := fun ⟨_, h, _⟩ => hS h
    simp [o_post, h0, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, hn]

open Classical in
theorem high_verify_spec (h : Runs) (hs : RunsSha512) (vk : high.ed25519.Ed25519VerifyingKey) (A : EdPoint)
    (hp : HoldsPoint vk A) (sig msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    high.ed25519.Ed25519VerifyingKey.verify vk sig msg ⦃ r =>
      r = if ed25519Verifies A (mid.ed25519.VerifyingKey.bytes vk).val msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.ed25519.Ed25519VerifyingKey.verify
  step with new_public_spec h
  step with try_from_shared_spec 64#usize sig as ⟨r, hr⟩
  by_cases hl : sig.length = 64
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨a, rfl, ha⟩ := hr
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with mid_verify_spec hs vk A hp a msg hm as ⟨r, hr⟩
    rw [hr, ha]
  · simp only [hl, ↓reduceIte] at hr
    obtain ⟨e, rfl⟩ := hr
    have hn : ¬ ed25519Verifies A (mid.ed25519.VerifyingKey.bytes vk).val msg.val sig.val :=
      fun ⟨h64, _⟩ => hl h64
    simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      high.ed25519.Ed25519VerifyingKey.verify.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, hn]

/-! ## Signing, `mid::ed25519::SigningKey` -/

/-- A signing key whose private key is the 32-byte `seed`: RFC 8032 5.1.5's
expansion of it, its secret scalar reduced mod L, with its public key's dalek
point. -/
def SeedKey (k : mid.ed25519.SigningKey) (seed : List U8) : Prop :=
  k.seed.val = seed ∧ k.s.bytes.asNat 8 = ed25519Scalar seed % n25519 ∧
    k.«prefix».val = (sha512 seed).drop 32 ∧ k.verifying_key.bytes.val = ed25519PublicKey seed ∧
    HoldsPoint k.verifying_key (edPow edB (ed25519Scalar seed))

theorem from_seed_spec (hs : RunsSha512) (seed : Std.Array U8 32#usize) :
    mid.ed25519.SigningKey.from_seed seed ⦃ k => SeedKey k seed.val ⦄ := by
  unfold mid.ed25519.SigningKey.from_seed low.ct.into_public low.ct.into_secret
  simp only [bind_ok]
  step as ⟨s, hs0⟩
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  step with ed25519_digest_spec hs s s1 s2 (by simp [Slice.length, hs0, hs1, hs2, Std.Array.empty]) as ⟨hh, hhv⟩
  step*
  case hs => rw [s4_post]; exact lt_trans (Nat.mod_lt _ L_pos) L_lt
  subst r_post r1_post
  simp only [core.result.Result.Ok.injEq] at *
  subst_vars
  have hH : hh.val = sha512 seed.val := by
    rw [hhv]
    simp [Array.val_to_slice, Std.Array.empty]
  have hsc : Array.asNat 8 a1 = ed25519Scalar seed.val := by
    rw [asNat_eq_leNat, a1_post, r_post1, lower_post2, Array.val_to_slice, hH, ed25519Scalar]
  have hpt : ofDalek point.toPoint = edPow edB (ed25519Scalar seed.val) := by
    rw [point_post1, s4_post, hsc, ofDalek_nsmul_basepoint]
  dsimp only [SeedKey, HoldsPoint, Holds]
  refine ⟨rfl, ?_, ?_, ?_, point_post, hpt⟩
  · rw [s4_post, hsc, L_eq]
  · rw [r1_post1, lower_post3, Array.val_to_slice, hH]
  · rw [encode_val cey _ cey_post, hpt]
    rfl

theorem sign_mod (k a r n : Nat) : (k * (a % n) % n + r) % n = (k * a + r) % n := by
  have h1 : k * (a % n) % n ≡ k * a [MOD n] := (Nat.mod_modEq _ n).trans ((Nat.mod_modEq a n).mul_left k)
  exact h1.add_right r

/-- `sign` with a key whose private key is `seed`: RFC 8032's signature. -/
theorem mid_sign_spec (hs : RunsSha512) (sk : mid.ed25519.SigningKey) (seed : List U8)
    (hk : SeedKey sk seed) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    mid.ed25519.SigningKey.sign sk msg ⦃ sig => sig.val = ed25519Sign seed msg.val ⦄ := by
  obtain ⟨-, hks, hkp, hkb, -⟩ := hk
  unfold mid.ed25519.SigningKey.sign low.ct.into_public curve25519_dalek.scalar.Scalar.as_bytes
  step as ⟨s, hs0⟩
  step as ⟨s1, hs1⟩
  step with ed25519_digest_spec hs s msg s1 (by simp [Slice.length, hs0, hs1, Std.Array.empty] at *; omega)
    as ⟨rh, hrh⟩
  step*
  case hs => rw [r_post]; exact lt_trans (Nat.mod_lt _ L_pos) L_lt
  case ha => rw [s4_post]; exact Nat.mod_lt _ L_pos
  case hb => rw [r_post]; exact Nat.mod_lt _ L_pos
  have hceyl : cey.val.length = 32 := cey.property
  have ha4l : s5.bytes.val.length = 32 := s5.bytes.property
  have hsig : (index_mut_back1 s11).val = cey.val ++ s5.bytes.val := by
    have hz : (Array.repeat 64#usize 0#u8).val = [] ++ List.replicate 64 0#u8 := by simp [Array.repeat]
    rw [s9_post2, s6_post2, s11_post, s10_post, s8_post, s7_post, hz, Array.val_to_slice,
      setSlice!_at [] _ _ 0 rfl (by simp [hceyl])]
    simp only [List.nil_append, Array.val_to_slice]
    rw [setSlice!_at _ _ _ 32 hceyl (by simp [ha4l, hceyl])]
    simp [ha4l, hceyl]
  have hR : cey.val = leBytesOf 32 (edEncode (edPow edB
      (leNat (sha512 ((sha512 seed).drop 32 ++ msg.val)) % n25519))) := by
    rw [encode_val cey _ cey_post, ep_post1, ofDalek_nsmul, ofDalek_basepoint, r_post, asNat_eq_leNat, hrh, hs0,
      hs1, Array.val_to_slice, hkp, L_eq]
    simp [Array.val_to_slice, Std.Array.empty]
  have hS : Array.asNat 8 s5.bytes = (leNat (sha512 (cey.val ++ ed25519PublicKey seed ++ msg.val)) % n25519 *
      ed25519Scalar seed + leNat (sha512 ((sha512 seed).drop 32 ++ msg.val)) % n25519) % n25519 := by
    rw [s5_post, s4_post, k1_post, hks, r_post, L_eq, sign_mod]
    simp only [asNat_eq_leNat, k_post, hrh, s2_post, s3_post, hs0, hs1, Array.val_to_slice, hkb, hkp]
    simp [Std.Array.empty]
  have hsl : s5.bytes.val = leBytesOf 32 (Array.asNat 8 s5.bytes) := by
    have := leBytesOf_leNat s5.bytes.val
    rw [ha4l] at this
    exact this.symm
  rw [hsig, hsl, hS, hR]
  simp only [ed25519Sign]

/-! ## The Ed25519 keys, `high::ed25519` -/

theorem high_sign_spec (h : Runs) (hs : RunsSha512) (k : high.ed25519.Ed25519SigningKey) (seed : List U8)
    (hk : SeedKey k seed) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    high.ed25519.Ed25519SigningKey.sign k msg ⦃ sig => sig.val = ed25519Sign seed msg.val ⦄ := by
  unfold high.ed25519.Ed25519SigningKey.sign
  step with new_secret_spec h
  exact mid_sign_spec hs k seed hk msg hm

/-- The public key of a signing key is its verifying key: cloning dalek's
point copies it. -/
theorem high_public_key_spec (h : Runs) (k : high.ed25519.Ed25519SigningKey) :
    high.ed25519.Ed25519SigningKey.public_key k ⦃ vk => vk = k.verifying_key ⦄ := by
  unfold high.ed25519.Ed25519SigningKey.public_key mid.ed25519.SigningKey.impl.verifying_key
    mid.ed25519.VerifyingKey.Insts.CoreCloneClone.clone
    curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCloneClone.clone
  step with new_public_spec h
  step*
  subst_vars
  cases k with | mk _ _ _ vk => cases vk; simp_all

theorem key_pair_new_spec (h : Runs) (k : high.ed25519.Ed25519SigningKey) :
    high.signature.ed25519.KeyPair.new k ⦃ kp => kp.key = k ∧ kp.«public» = k.verifying_key ⦄ := by
  unfold high.signature.ed25519.KeyPair.new
  step with high_public_key_spec h k as ⟨vk, hvk⟩
  exact hvk

/-- A key pair whose private key is the 32-byte `seed`, holding its public
key. -/
def KeyPairOf (kp : high.signature.ed25519.KeyPair) (seed : List U8) : Prop :=
  SeedKey kp.key seed ∧ kp.«public» = kp.key.verifying_key

theorem high_seed_from_bytes_spec (h : Runs) (hs : RunsSha512) (seed : Slice U8) :
    high.ed25519.Ed25519SigningKey.from_bytes seed ⦃ r =>
      if seed.length = 32 then ∃ k, r = .Ok k ∧ SeedKey k seed.val
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.ed25519.Ed25519SigningKey.from_bytes
  step with new_secret_spec h
  step with core.array.TryFromArrayCopySlice.try_from.step 32#usize core.marker.CopyU8 seed as ⟨r, hr⟩
  by_cases hl : seed.length = 32
  · simp only [hl, ↓reduceIte]
    rcases r with a | e
    · obtain ⟨ha, -⟩ := hr
      simp only [core.result.Result.map,
        high.ed25519.Ed25519SigningKey.from_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU832Ed25519SigningKey.call_once]
      step with from_seed_spec hs a as ⟨k, hk⟩
      simp only [core.result.Result.map_err]
      rw [ha] at hk
      simp [hk]
    · exact absurd hl hr
  · simp only [hl, ↓reduceIte]
    rcases r with a | e
    · have := a.property
      exact absurd (by simp_all [Slice.length]) hl
    · simp [core.result.Result.map, core.result.Result.map_err,
        high.ed25519.Ed25519SigningKey.from_bytes.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once,
        core.convert.IntoFrom.into, error.Error.Insts.CoreConvertFromKeyFormatError.from]

theorem high_generate_spec (h : Runs) (hs : RunsSha512) (r : core.result.Result Unit getrandom.error.Error)
    (out : Slice U8) (hout : out.length = 32)
    (hfill : getrandom.fill (Array.repeat 32#usize 0#u8).to_slice = ok (r, out)) :
    high.ed25519.Ed25519SigningKey.generate ⦃ key =>
      match r with
      | .Ok _ => ∃ k, key = core.result.Result.Ok k ∧ SeedKey k out.val
      | .Err _ => key = core.result.Result.Err error.Error.RngFailed ⦄ := by
  unfold high.ed25519.Ed25519SigningKey.generate mid.rng.SystemRandom.Insts.RindMidRngRandomSource.fill
  rcases r with _ | e <;> simp only [Array.to_slice_mut, lift] <;> step with new_secret_spec h <;> rw [hfill]
  · simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]
    have hfrom : ((Array.repeat 32#usize 0#u8).from_slice out).val = out.val := by
      simp [Array.from_slice, hout]
    step with from_seed_spec hs _ as ⟨k, hk⟩
    rw [hfrom] at hk
    simp [hk]
  · simp [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      mid.rng.RandomSourceSystemRandom.fill.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-! ## The signature API, `high::signature::ed25519` -/

/-- A generated key pair's private key is the 32 bytes the random source drew,
and a failed draw is refused. The draw itself is outside the functional spec. -/
theorem ed25519_generate (h : Runs) (hs : RunsSha512) (r : core.result.Result Unit getrandom.error.Error)
    (out : Slice U8) (hout : out.length = 32)
    (hfill : getrandom.fill (Array.repeat 32#usize 0#u8).to_slice = ok (r, out)) :
    high.signature.ed25519.KeyPair.generate ⦃ kp =>
      match r with
      | .Ok _ => ∃ k, kp = core.result.Result.Ok k ∧ KeyPairOf k out.val
      | .Err _ => kp = core.result.Result.Err error.Error.RngFailed ⦄ := by
  unfold high.signature.ed25519.KeyPair.generate
  step with high_generate_spec h hs r out hout hfill as ⟨key, hkey⟩
  rcases r with _ | _ <;> simp only at hkey ⊢
  · obtain ⟨k, rfl, hk⟩ := hkey
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    step with key_pair_new_spec h k as ⟨kp, hkp1, hkp2⟩
    exact ⟨kp, rfl, by rw [hkp1]; exact hk, by rw [hkp1]; exact hkp2⟩
  · subst hkey
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

open Classical in
/-- A key pair loaded from a seed and the public key it claims: refused unless
the seed is 32 bytes and the public key is the seed's, and otherwise its
private key is the seed. -/
theorem ed25519_from_seed_and_public_key (h : Runs) (hs : RunsSha512) (seed pk : Slice U8) :
    high.signature.ed25519.KeyPair.from_seed_and_public_key seed pk ⦃ r =>
      if seed.length = 32 then
        if ed25519PublicKey seed.val = pk.val then ∃ kp, r = .Ok kp ∧ KeyPairOf kp seed.val
        else r = .Err (.KeyRejected .MismatchedPublicKey)
      else r = .Err (.KeyRejected .WrongLength) ⦄ := by
  unfold high.signature.ed25519.KeyPair.from_seed_and_public_key
  step with high_seed_from_bytes_spec h hs seed as ⟨r, hr⟩
  by_cases hl : seed.length = 32
  · simp only [hl, ↓reduceIte] at hr ⊢
    obtain ⟨k, rfl, hk⟩ := hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    step with key_pair_new_spec h k as ⟨kp, hkp1, hkp2⟩
    have hkb : (mid.ed25519.VerifyingKey.bytes kp.«public»).val = pk.val ↔ ed25519PublicKey seed.val = pk.val := by
      rw [hkp2, hk.2.2.2.1]
    unfold high.signature.ed25519.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref
      high.ed25519.Ed25519VerifyingKey.bytes mid.ed25519.VerifyingKey.impl.bytes
    by_cases hCc : ed25519PublicKey seed.val = pk.val
    · simp only [hCc, ↓reduceIte]
      step*
      simp_all [KeyPairOf]
    · simp only [hCc, ↓reduceIte]
      step*
      simp_all [error.Error.Insts.CoreConvertFromKeyFormatError.from]
  · simp only [hl, ↓reduceIte] at hr ⊢
    subst hr
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- An Ed25519 signature's bytes: RFC 8032's PureEd25519 signature of the
message under the key pair's seed, for messages under 2⁶⁴ - 64 bytes. -/
theorem ed25519_sign (h : Runs) (hs : RunsSha512) (kp : high.signature.ed25519.KeyPair) (seed : List U8)
    (hkp : KeyPairOf kp seed) (msg : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    (do
      let sig ← high.signature.ed25519.KeyPair.sign kp msg
      high.signature.ed25519.Signature.Insts.CoreConvertAsRefSliceU8.as_ref sig) ⦃ b =>
      b.val = ed25519Sign seed msg.val ⦄ := by
  unfold high.signature.ed25519.KeyPair.sign high.signature.ed25519.Signature.Insts.CoreConvertAsRefSliceU8.as_ref
  step with high_sign_spec h hs kp.key seed hkp.1 msg hm as ⟨a, ha⟩
  simpa [Array.val_to_slice] using ha

/-- A key pair's public key's bytes: RFC 8032's public key of its seed. -/
theorem ed25519_key_pair_public_key (kp : high.signature.ed25519.KeyPair) (seed : List U8)
    (hkp : KeyPairOf kp seed) :
    (do
      let pk ← high.signature.ed25519.KeyPair.public_key kp
      high.signature.ed25519.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref pk) ⦃ b =>
      b.val = ed25519PublicKey seed ⦄ := by
  unfold high.signature.ed25519.KeyPair.public_key high.signature.ed25519.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref
    high.ed25519.Ed25519VerifyingKey.bytes mid.ed25519.VerifyingKey.impl.bytes
  obtain ⟨⟨-, -, -, hkb, -⟩, hpub⟩ := hkp
  simp only [bind_ok, WP.spec_ok, Array.val_to_slice]
  rw [hpub]
  exact hkb

open Classical in
/-- Verification with a key pair's public key: RFC 8032's verification with
its seed's public key, whose point is the base point times its secret scalar. -/
theorem ed25519_key_pair_verify (h : Runs) (hs : RunsSha512) (kp : high.signature.ed25519.KeyPair)
    (seed : List U8) (hkp : KeyPairOf kp seed) (msg sig : Slice U8) (hm : msg.length + 64 < 2 ^ 64) :
    (do
      let pk ← high.signature.ed25519.KeyPair.public_key kp
      high.signature.ed25519.PublicKey.verify pk msg sig) ⦃ r =>
      r = if ed25519Verifies (edPow edB (ed25519Scalar seed)) (ed25519PublicKey seed) msg.val sig.val then
        (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄ := by
  unfold high.signature.ed25519.KeyPair.public_key high.signature.ed25519.PublicKey.verify
  obtain ⟨⟨-, -, -, hkb, hkpt⟩, hpub⟩ := hkp
  simp only [bind_ok]
  have hb : (mid.ed25519.VerifyingKey.bytes kp.«public»).val = ed25519PublicKey seed := by rw [hpub]; exact hkb
  rw [← hb]
  exact high_verify_spec h hs kp.«public» _ (by rw [hpub]; exact hkpt) sig msg hm

open Classical in
/-- An Ed25519 public key parsed from its encoding: refused unless it is 32
bytes, refused if its y-coordinate is one of libsodium's small-order list,
refused unless it encodes a point of the group, and otherwise its
verification is RFC 8032's with that point, for messages under 2⁶⁴ - 64
bytes. -/
theorem ed25519_public_key_new (h : Runs) (hs : RunsSha512) (key : Slice U8) :
    high.signature.ed25519.PublicKey.new key ⦃ r =>
      if key.length ≠ 32 then r = .Err (.KeyRejected .WrongLength)
      else if leNat key.val % 2 ^ 255 ∈ edSmallOrderY then r = .Err (.KeyRejected .SmallOrder)
      else if edValidEncode (leNat key.val) then
        ∃ pk, r = .Ok pk ∧ ∀ msg sig : Slice U8, msg.length + 64 < 2 ^ 64 →
          high.signature.ed25519.PublicKey.verify pk msg sig ⦃ v =>
            v = if ed25519Verifies (edDecode (leNat key.val)) key.val msg.val sig.val then
              (.Ok () : core.result.Result Unit error.Error) else .Err .BadSignature ⦄
      else r = .Err (.KeyRejected .NotOnCurve) ⦄ := by
  unfold high.signature.ed25519.PublicKey.new
  step with high_from_bytes_spec h hs key as ⟨r, hr⟩
  split_ifs at hr ⊢ with hl hso hv
  · subst hr; simp [core.result.Result.map]
  · subst hr; simp [core.result.Result.map]
  · obtain ⟨vk, rfl, hvb, hvp⟩ := hr
    simp only [core.result.Result.map, P.Insts.CoreOpsFunctionFnOnceTupleEd25519VerifyingKeyPublicKey.call_once,
      high.signature.ed25519.PublicKey.constructor, bind_ok, WP.spec_ok]
    refine ⟨_, rfl, fun msg sig hm => ?_⟩
    simp only [high.signature.ed25519.PublicKey.verify]
    have := high_verify_spec h hs vk _ hvp sig msg hm
    rwa [hvb] at this
  · subst hr; simp [core.result.Result.map]

end rind.armv7
