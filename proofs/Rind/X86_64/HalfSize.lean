import Rind.X86_64.Funs
import Rind.RsaLemmas
import Rind.Ed25519
import Rind.Bytes
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.GCD
open Aeneas Aeneas.Std Result rind.spec

/-!
# Half-size scalars, `mid::half_size::split`

`split_spec` proves that `split` of a `k < 2^255` returns `u` and `v` with
`u ≡ v k (mod 8L)`, `v` odd and below 2^128, and `|u| < 2^255`: what Ed25519
verification's half-size check, `Rind.Ed25519Group`'s `half_size_iff`, needs
of them, and the multi-scalar multiplication's bound on its scalars. That the
two parts usually come out near 128 bits, though not always (`u` can stay near
2^255), only bounds the work, so nothing proves it.

The extended Euclidean loop keeps, for its rows `(r, t)`, `r ≡ ±t k (mod 8L)`
with opposite signs, the two `t` coprime, and `r₀ |t₁| + r₁ |t₀| = 8L`, as
`split`'s comments argue; the last bounds each `t` while the loop runs.
-/

namespace rind.x86_64

namespace HalfSize

open mid.half_size

/-- `8L`. -/
def N : Nat := 8 * n25519

/-- The number a `U256` holds. -/
def val (x : U256) : Nat := 2 ^ 128 * x.hi.val + x.lo.val

/-- The bits a number needs, as `bits` counts them. -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log 2 x + 1

theorem lt_pow_bitLen (x : Nat) : x < 2 ^ bitLen x := by
  unfold bitLen; split_ifs with h
  · simp [h]
  · exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem pow_bitLen_le {x : Nat} (hx : 0 < x) : 2 ^ (bitLen x - 1) ≤ x := by
  unfold bitLen; rw [ite_eq_right (show ¬ x = 0 by omega), Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (by omega)

theorem bitLen_le {x m : Nat} (h : x < 2 ^ m) : bitLen x ≤ m := by
  unfold bitLen; split_ifs with h0
  · omega
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem bitLen_mono {x y : Nat} (h : x ≤ y) : bitLen x ≤ bitLen y :=
  bitLen_le (lt_of_le_of_lt h (lt_pow_bitLen y))

theorem bitLen_eq {x m : Nat} (hm : 0 < m) (h1 : 2 ^ (m - 1) ≤ x) (h2 : x < 2 ^ m) : bitLen x = m := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h1
  have h3 := bitLen_le h2
  have h4 := lt_pow_bitLen x
  have : m - 1 < bitLen x := by
    by_contra hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show bitLen x ≤ m - 1 by omega)
    omega
  omega

theorem bitLen_pos {x : Nat} (hx : 0 < x) : 0 < bitLen x := by
  unfold bitLen; rw [ite_eq_right (show ¬ x = 0 by omega)]; omega

@[step]
theorem bits_spec (x : U128) : mid.half_size.bits x ⦃ r => r.val = bitLen x.val ⦄ := by
  unfold mid.half_size.bits
  have hx := x.hBounds
  have hlz : (core.num.U128.leading_zeros x).val = if x.val = 0 then 128 else 128 - Nat.log 2 x.val - 1 := by
    simp only [core.num.U128.leading_zeros, BitVec.leadingZeros]
    by_cases h : x.val = 0
    · have : x.bv = 0 := by rw [← BitVec.toNat_inj]; simpa [U128.bv_toNat] using h
      simp [this, h]; rfl
    · have : x.bv ≠ 0 := by intro hb; apply h; rw [← U128.bv_toNat, hb]; rfl
      have hl : Nat.log 2 x.val < 128 := Nat.log_lt_of_lt_pow h (by simpa [UScalarTy.numBits] using hx)
      simp only [this, h, ↓reduceIte, U128.bv_toNat]
      show (BitVec.ofNat 32 _).toNat = _
      rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have hlog : x.val ≠ 0 → Nat.log 2 x.val < 128 := fun h =>
    Nat.log_lt_of_lt_pow h (by simpa [UScalarTy.numBits] using hx)
  have h128 : (128#u32 : U32).val = 128 := rfl
  simp only [lift, bind_ok]
  step as ⟨r, hr⟩
  · rw [h128]; split_ifs at hlz <;> simp only [hlz] <;> omega
  simp only [bitLen]
  rw [hr, hlz]
  split_ifs with h
  · rfl
  · have := hlog h; omega

theorem or_mul_pow (a b i : Nat) (hb : b < 2 ^ i) : b ||| a <<< i = b + 2 ^ i * a := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]; ring

theorem wordsNat_make4 (a b c d : U64) (h) :
    wordsNat (Std.Array.make 4#usize [a, b, c, d] h).val = a.val + 2 ^ 64 * (b.val + 2 ^ 64 * (c.val + 2 ^ 64 * d.val)) := by
  simp [wordsNat, Std.Array.make, Nat.ofDigits]

theorem u128_size : U128.size = 2 ^ 128 := by rw [U128.size_def, U128.numBits_def]; rfl

theorem shl64 (a : U64) : (a.val <<< 64) % U128.size = a.val <<< 64 := by
  apply Nat.mod_eq_of_lt
  have := a.hBounds
  simp only [UScalarTy.numBits] at this
  rw [Nat.shiftLeft_eq, u128_size]; omega

@[step]
theorem from_spec (x : Std.Array U64 4#usize) : U256.from x ⦃ r => val r = wordsNat x.val ⦄ := by
  unfold U256.from
  simp only [lift, bind_ok]
  step*
  have hl : x.val.length = 4 := x.property
  rw [wordsNat_four _ hl]
  simp only [val, UScalar.val_or, core.convert.num.FromU128U64.from_val_eq, i4_post, i10_post, shl64]
  have b0 := i.hBounds; have b1 := i6.hBounds
  simp only [UScalarTy.numBits] at b0 b1
  rw [or_mul_pow _ _ _ b0, or_mul_pow _ _ _ b1, i_post, i2_post, i6_post, i8_post]
  simp only [getElem!_pos x.val 0 (by omega), getElem!_pos x.val 1 (by omega), getElem!_pos x.val 2 (by omega),
    getElem!_pos x.val 3 (by omega)]
  ring

@[step]
theorem words_spec (x : U256) : U256.words x ⦃ r => wordsNat r.val = val x ⦄ := by
  unfold U256.words
  simp only [lift, bind_ok]
  step*
  rw [wordsNat_make4]
  have hlo := x.lo.hBounds
  have hhi := x.hi.hBounds
  simp only [UScalarTy.numBits] at hlo hhi
  simp only [UScalar.cast_val_eq, val, UScalarTy.numBits, i1_post, i4_post, Nat.shiftRight_eq_div_pow]
  omega

@[step]
theorem sub_spec (x y : U256) (h : val y ≤ val x) : U256.sub x y ⦃ r => val r = val x - val y ⦄ := by
  unfold U256.sub
  have hxl := x.lo.hBounds
  have hyl := y.lo.hBounds
  simp only [UScalarTy.numBits] at hxl hyl
  unfold val at h
  simp only [lift, bind_ok]
  have hlo := core.num.U128.overflowing_sub_eq x.lo y.lo
  generalize core.num.U128.overflowing_sub x.lo y.lo = z at hlo ⊢
  obtain ⟨lo, borrow⟩ := z
  simp only at hlo ⊢
  have h1 : (1#u128 : U128).val = 1 := rfl
  have h0 : (0#u128 : U128).val = 0 := rfl
  step as ⟨i, hi⟩
  split_ifs at hlo with hlt
  · obtain ⟨hl, rfl⟩ := hlo
    have hl' : lo.val + y.lo.val = x.lo.val + 2 ^ 128 := by rw [← u128_size, ← UScalar.size_UScalarTyU128]; exact hl
    simp only [core.convert.num.FromU128Bool.from, ↓reduceIte]
    step as ⟨i2, hi2⟩
    unfold val; simp only; omega
  · obtain ⟨hl, rfl⟩ := hlo
    simp only [core.convert.num.FromU128Bool.from, Bool.false_eq_true, ↓reduceIte]
    step as ⟨i2, hi2⟩
    unfold val; simp only; omega

theorem val_lt (x : U256) : val x < 2 ^ 256 := by
  have := x.hi.hBounds; have := x.lo.hBounds
  simp only [UScalarTy.numBits] at *
  unfold val; omega

@[step]
theorem bits256_spec (x : U256) : U256.bits x ⦃ r => r.val = bitLen (val x) ⦄ := by
  unfold U256.bits
  have hlo := x.lo.hBounds; have hhi := x.hi.hBounds
  simp only [UScalarTy.numBits] at hlo hhi
  split
  · rename_i h
    have h0 : x.hi.val = 0 := by rw [h]; rfl
    step as ⟨r, hr⟩
    rw [hr]; unfold val; rw [h0]; simp
  · rename_i h
    have h0 : x.hi.val ≠ 0 := fun h' => h ((UScalar.eq_equiv _ _).mpr (by rw [h']; rfl))
    step as ⟨b, hb⟩
    have hb128 : b.val ≤ 128 := by rw [hb]; exact bitLen_le hhi
    step as ⟨r, hr⟩
    rw [hr, hb]
    have hpos : 0 < x.hi.val := by omega
    have e1 := pow_bitLen_le hpos
    have e2 := lt_pow_bitLen x.hi.val
    have e3 := bitLen_pos hpos
    symm
    apply bitLen_eq (by omega)
    · rw [show 128 + bitLen x.hi.val - 1 = 128 + (bitLen x.hi.val - 1) by omega, pow_add]
      unfold val; nlinarith
    · rw [pow_add]; unfold val; nlinarith

/-- `U256`'s `Ord`, which compares the numbers. -/
theorem cmp_eq (x y : U256) : U256.Insts.CoreCmpOrd.cmp x y = ok (compare (val x) (val y)) := by
  unfold U256.Insts.CoreCmpOrd.cmp
  have := x.lo.hBounds; have := y.lo.hBounds
  simp only [UScalarTy.numBits] at *
  simp only [lift, bind_ok, core.cmp.impls.OrdU128.cmp]
  rcases lt_trichotomy x.hi.val y.hi.val with h | h | h
  · have hc : compare x.hi.val y.hi.val = .lt := compare_lt_iff_lt.mpr h
    rw [hc]; simp only
    rw [compare_lt_iff_lt.mpr (by unfold val; omega)]
  · have hc : compare x.hi.val y.hi.val = .eq := compare_eq_iff_eq.mpr h
    rw [hc]; simp only
    unfold val; rw [h]
    rcases lt_trichotomy x.lo.val y.lo.val with h' | h' | h'
    · rw [compare_lt_iff_lt.mpr h', compare_lt_iff_lt.mpr (by omega)]
    · rw [compare_eq_iff_eq.mpr h', compare_eq_iff_eq.mpr (by omega)]
    · rw [compare_gt_iff_gt.mpr h', compare_gt_iff_gt.mpr (by omega)]
  · have hc : compare x.hi.val y.hi.val = .gt := compare_gt_iff_gt.mpr h
    rw [hc]; simp only
    rw [compare_gt_iff_gt.mpr (by unfold val; omega)]

@[step]
theorem gt_spec (x y : U256) :
    core.cmp.PartialOrd.gt.trait_default U256.Insts.CoreCmpPartialOrdU256 x y ⦃ b => b ↔ val y < val x ⦄ := by
  simp only [core.cmp.PartialOrd.gt.trait_default, core.cmp.PartialOrd.gt.default, core.cmp.PartialOrd.gt_body,
    U256.Insts.CoreCmpPartialOrdU256.partial_cmp, cmp_eq, bind_ok]
  simp [compare_gt_iff_gt]

@[step]
theorem lt_spec (x y : U256) :
    core.cmp.PartialOrd.lt.trait_default U256.Insts.CoreCmpPartialOrdU256 x y ⦃ b => b ↔ val x < val y ⦄ := by
  simp only [core.cmp.PartialOrd.lt.trait_default, core.cmp.PartialOrd.lt.default, core.cmp.PartialOrd.lt_body,
    U256.Insts.CoreCmpPartialOrdU256.partial_cmp, cmp_eq, bind_ok]
  simp [compare_lt_iff_lt]

theorem mul_pow_div (lo s : Nat) (hs : s ≤ 128) : lo * 2 ^ s / 2 ^ 128 = lo / 2 ^ (128 - s) := by
  rw [show 2 ^ 128 = 2 ^ s * 2 ^ (128 - s) by rw [← pow_add]; congr 1; omega, mul_comm lo,
    Nat.mul_div_mul_left _ _ (by positivity)]

@[step]
theorem shl_spec (x : U256) (s : U32) (hs : s.val < 128) (h : val x * 2 ^ s.val < 2 ^ 256) :
    U256.shl x s ⦃ r => val r = val x * 2 ^ s.val ⦄ := by
  unfold U256.shl
  have hlo := x.lo.hBounds; have hhi := x.hi.hBounds
  simp only [UScalarTy.numBits] at hlo hhi
  split
  · rw [show ((0#32#uscalar : U32) : Nat) = 0 from rfl]; simp
  · rename_i h0
    have hs0 : s.val ≠ 0 := fun h' => h0 ((UScalar.eq_equiv _ _).mpr (by rw [h']; rfl))
    have hhi' : x.hi.val * 2 ^ s.val < 2 ^ 128 := by
      unfold val at h
      have : 2 ^ 128 * (x.hi.val * 2 ^ s.val) < 2 ^ 128 * 2 ^ 128 := by
        calc 2 ^ 128 * (x.hi.val * 2 ^ s.val) = (2 ^ 128 * x.hi.val) * 2 ^ s.val := by ring
          _ ≤ (2 ^ 128 * x.hi.val + x.lo.val) * 2 ^ s.val := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
          _ < 2 ^ 256 := h
          _ = _ := by norm_num
      exact Nat.lt_of_mul_lt_mul_left this
    have h128 : (128#u32 : U32).val = 128 := rfl
    simp only [lift, bind_ok]
    step*
    unfold val
    simp only [UScalar.val_or, *]
    rw [u128_size, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhi', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hq : x.lo.val / 2 ^ (128 - s.val) < 2 ^ s.val := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show s.val + (128 - s.val) = 128 by omega]
      exact hlo
    have hor : x.hi.val * 2 ^ s.val ||| x.lo.val / 2 ^ (128 - s.val) =
        x.lo.val / 2 ^ (128 - s.val) + 2 ^ s.val * x.hi.val := by
      rw [Nat.lor_comm, ← Nat.shiftLeft_eq, or_mul_pow _ _ _ hq]
    rw [hor]
    have hsplit := Nat.div_add_mod (x.lo.val * 2 ^ s.val) (2 ^ 128)
    rw [mul_pow_div _ _ (by omega)] at hsplit
    nlinarith

/-! ## The Euclidean loop's invariant -/

theorem N_eq : N = 57896044618658097711785492504343953926856930875039260848015607506283634007912 := by
  simp [N, n25519]

theorem N_lt : N < 2 ^ 256 := by rw [N_eq]; norm_num

theorem N_gt : 2 ^ 255 < N := by rw [N_eq]; norm_num

/-- `r ≡ ±t k (mod 8L)`, `+` for the row from `k`. -/
def Congr (K r t : Nat) (from_k : Bool) : Prop :=
  (r : Int) ≡ (if from_k then (t : Int) else -(t : Int)) * K [ZMOD N]

/-- What `split`'s loop keeps of its two rows, for `k`'s number `K`. -/
structure Inv (K : Nat) (big small : Row) : Prop where
  sign : big.from_k = !small.from_k
  cb : Congr K (val big.r) big.t.val big.from_k
  cs : Congr K (val small.r) small.t.val small.from_k
  cop : Nat.Coprime big.t.val small.t.val
  sum : val big.r * small.t.val + val small.r * big.t.val = N
  le : val small.r ≤ val big.r
  big_ge : 2 ^ 128 ≤ val big.r
  big_le : val big.r ≤ N
  small_lt : val small.r < 2 ^ 255
  big_lt : val big.r < 2 ^ 255 ∨ small.t.val = 1

/-- Subtracting `2^sh` times the smaller row from the bigger keeps the `t`
below 2^128, while the smaller row is at least 2^128. -/
theorem t_bound {K : Nat} {big small : Row} (h : Inv K big small) (hs : 2 ^ 128 ≤ val small.r) (sh : Nat)
    (hsh : val small.r * 2 ^ sh ≤ val big.r) :
    big.t.val + small.t.val * 2 ^ sh < 2 ^ 128 := by
  have hsum := h.sum
  have e : (val big.r - val small.r * 2 ^ sh) * small.t.val + val small.r * (big.t.val + small.t.val * 2 ^ sh) = N := by
    rw [← hsum, Nat.sub_mul]
    have : val small.r * 2 ^ sh * small.t.val ≤ val big.r * small.t.val := Nat.mul_le_mul_right _ hsh
    zify [this, hsh]; ring
  have h1 : val small.r * (big.t.val + small.t.val * 2 ^ sh) ≤ N := by omega
  have h2 : 2 ^ 128 * (big.t.val + small.t.val * 2 ^ sh) ≤ N :=
    le_trans (Nat.mul_le_mul_right _ hs) h1
  have := N_lt
  by_contra hc
  have : 2 ^ 128 * 2 ^ 128 ≤ 2 ^ 128 * (big.t.val + small.t.val * 2 ^ sh) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem congr_step {K rb rs tb ts : Nat} {fb fs : Bool} (hf : fb = !fs) (hb : Congr K rb tb fb)
    (hs : Congr K rs ts fs) (sh : Nat) (hle : rs * 2 ^ sh ≤ rb) :
    Congr K (rb - rs * 2 ^ sh) (tb + ts * 2 ^ sh) fb := by
  unfold Congr at *
  have e := Int.ModEq.sub hb (hs.mul_right (2 ^ sh))
  push_cast [hle]
  refine e.trans ?_
  unfold Int.ModEq
  congr 1
  subst hf
  cases fs <;> simp <;> ring

theorem inv_step {K : Nat} {big small : Row} (h : Inv K big small) (hs : 2 ^ 128 ≤ val small.r) (sh : Nat)
    (hsh1 : val small.r * 2 ^ sh ≤ val big.r) (hsh2 : val big.r < val small.r * 2 ^ (sh + 1))
    (r' : U256) (hr' : val r' = val big.r - val small.r * 2 ^ sh)
    (t' : U128) (ht' : t'.val = big.t.val + small.t.val * 2 ^ sh) :
    (val r' < val small.r → Inv K small { big with r := r', t := t' }) ∧
      (¬ val r' < val small.r → Inv K { big with r := r', t := t' } small) ∧
      val r' + val small.r < val big.r + val small.r := by
  have hsum := h.sum
  have hpos : 0 < val small.r := by omega
  have hsh0 : val small.r ≤ val small.r * 2 ^ sh := Nat.le_mul_of_pos_right _ (by positivity)
  have hhalf : 2 * val r' < val big.r := by
    rw [hr']; rw [pow_succ, ← Nat.mul_assoc] at hsh2; omega
  have hN := N_lt
  have hbig := h.big_le
  have hcop : Nat.Coprime t'.val small.t.val := by
    rw [ht']; exact (Nat.coprime_add_mul_left_left _ _ _).mpr h.cop
  have hc := congr_step h.sign h.cb h.cs sh hsh1
  rw [← hr', ← ht'] at hc
  have hid : val r' * small.t.val + val small.r * t'.val = N := by
    rw [hr', ht', ← hsum, Nat.sub_mul]
    have : val small.r * 2 ^ sh * small.t.val ≤ val big.r * small.t.val := Nat.mul_le_mul_right _ hsh1
    zify [this, hsh1]; ring
  refine ⟨fun hlt => ?_, fun hge => ?_, by omega⟩
  · exact {
      sign := by simp [h.sign]
      cb := h.cs
      cs := hc
      cop := hcop.symm
      sum := by simp only; rw [← hid]; ring
      le := hlt.le
      big_ge := hs
      big_le := by have := h.le; omega
      small_lt := by simp only; omega
      big_lt := Or.inl h.small_lt }
  · exact {
      sign := h.sign
      cb := hc
      cs := h.cs
      cop := hcop
      sum := hid
      le := by simp only; omega
      big_ge := by simp only; omega
      big_le := by simp only; omega
      small_lt := h.small_lt
      big_lt := Or.inl (by simp only; omega) }

theorem bitLen_ge_129 {x : Nat} (h : 2 ^ 128 ≤ x) : 129 ≤ bitLen x := by
  by_contra hc
  have := lt_pow_bitLen x
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show bitLen x ≤ 128 by omega)
  omega

/-- The largest shift with `small << shift <= big`, as the loop picks it. -/
theorem shift_facts {big small : Nat} (hs : 2 ^ 128 ≤ small) (hle : small ≤ big) (hbig : big < 2 ^ 256) :
    let shift := bitLen big - bitLen small
    shift < 128 ∧ small * 2 ^ shift < 2 ^ 256 ∧
      (big < small * 2 ^ shift → 1 ≤ shift ∧ small * 2 ^ (shift - 1) ≤ big ∧ big < small * 2 ^ (shift - 1 + 1)) ∧
      (¬ big < small * 2 ^ shift → big < small * 2 ^ (shift + 1)) := by
  intro shift
  have h1 := bitLen_ge_129 hs
  have h2 := bitLen_le hbig
  have h3 := bitLen_mono hle
  have hsl := lt_pow_bitLen small
  have hbl := lt_pow_bitLen big
  have hbp := pow_bitLen_le (show 0 < big by omega)
  have hsp := pow_bitLen_le (show 0 < small by omega)
  have hsum : bitLen small + shift = bitLen big := by omega
  have hlt : small * 2 ^ shift < 2 ^ bitLen big := by
    rw [← hsum, pow_add]; exact Nat.mul_lt_mul_of_pos_right hsl (by positivity)
  refine ⟨by omega, lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) h2), fun hb => ?_, fun hb => ?_⟩
  · have h0 : 1 ≤ shift := by
      by_contra h0
      have : shift = 0 := by omega
      rw [this, pow_zero, mul_one] at hb; omega
    refine ⟨h0, ?_, by rw [Nat.sub_add_cancel h0]; exact hb⟩
    have : small * 2 ^ (shift - 1) < 2 ^ (bitLen big - 1) := by
      rw [show bitLen big - 1 = bitLen small + (shift - 1) by omega, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hsl (by positivity)
    omega
  · calc big < 2 ^ bitLen big := hbl
      _ = 2 * 2 ^ (bitLen small - 1) * 2 ^ shift := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      _ ≤ 2 * small * 2 ^ shift := by gcongr
      _ = small * 2 ^ (shift + 1) := by ring

theorem split_loop_spec (K : Nat) (big small : Row) (h : Inv K big small) :
    split_loop big small ⦃ r =>
      Inv K r.1 ⟨⟨r.2.1, r.2.2.1⟩, r.2.2.2.1, r.2.2.2.2⟩ ∧ r.2.1.val = 0 ⦄ := by
  unfold split_loop
  apply loop.spec_decr_nat (fun x => val x.1.r + val x.2.r) (fun x => Inv K x.1 x.2)
  · rintro ⟨big, small⟩ h
    simp only at h ⊢
    unfold split_loop.body
    by_cases hne : (small.r.hi != 0#u128) = true
    · rw [ite_eq_left hne]
      have hhi : small.r.hi.val ≠ 0 := by
        intro h0; simp only [bne_iff_ne, ne_eq] at hne
        exact hne ((UScalar.eq_equiv _ _).mpr (by rw [h0]; rfl))
      have hs : 2 ^ 128 ≤ val small.r := by unfold val; omega
      have hbig := val_lt big.r
      obtain ⟨hsh, hsmul, hgt, hngt⟩ := shift_facts hs h.le hbig
      have h3 := bitLen_mono h.le
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨shift, hshift⟩
      rw [hi, hi1] at hshift
      have hsh' : shift.val < 128 := by rw [hshift]; exact hsh
      have hsmul' : val small.r * 2 ^ shift.val < 2 ^ 256 := by rw [hshift]; exact hsmul
      step with shl_spec small.r shift hsh' hsmul' as ⟨u, hu⟩
      step as ⟨b, hb⟩
      rw [hu, hshift] at hb
      apply WP.spec_bind (Pₘ := fun shift1 : U32 =>
        val small.r * 2 ^ shift1.val ≤ val big.r ∧ val big.r < val small.r * 2 ^ (shift1.val + 1) ∧
          shift1.val ≤ shift.val)
      · split
        · rename_i hb'
          obtain ⟨h0, hle, hlt⟩ := hgt (hb.mp hb')
          rw [← hshift] at h0 hle hlt
          step as ⟨s1, hs1⟩
          rw [hs1]
          exact ⟨by simpa using hle, by simpa using hlt, by simp⟩
        · rename_i hb'
          simp only [WP.spec_ok]
          exact ⟨by rw [hshift]; exact not_lt.mp (fun h' => hb' (hb.mpr h')),
            by rw [hshift]; exact hngt (fun h' => hb' (hb.mpr h')), le_refl _⟩
      rintro shift1 ⟨hle1, hlt1, hs1le⟩
      have hsmul1 : val small.r * 2 ^ shift1.val < 2 ^ 256 :=
        lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs1le)) hsmul'
      have hsh1 : shift1.val < 128 := by omega
      have htb := t_bound h hs shift1.val hle1
      step with shl_spec small.r shift1 hsh1 hsmul1 as ⟨u1, hu1⟩
      step with sub_spec big.r u1 (by rw [hu1]; exact hle1) as ⟨u2, hu2⟩
      rw [hu1] at hu2
      have hsh1' : shift1.val < 128 := hsh1
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = small.t.val * 2 ^ shift1.val := by
        rw [hi2, Nat.shiftLeft_eq, u128_size]; exact Nat.mod_eq_of_lt (by omega)
      have hadd : big.t.val + i2.val ≤ U128.max := by
        rw [hi2v, U128.max_def, U128.numBits_def]; simp only [UScalarTy.numBits]; omega
      step as ⟨i3, hi3⟩
      rw [hi2v] at hi3
      step as ⟨b1, hb1⟩
      obtain ⟨hA, hB, hC⟩ := inv_step h hs shift1.val hle1 hlt1 u2 hu2 i3 hi3
      split
      · rename_i hb1t
        simp only [WP.spec_ok]
        exact ⟨hA (hb1.mp hb1t), by omega⟩
      · rename_i hb1t
        simp only [WP.spec_ok]
        exact ⟨hB (fun h' => hb1t (hb1.mpr h')), by omega⟩
    · rw [ite_eq_right hne]
      simp only [WP.spec_ok]
      have h0 : small.r.hi.val = 0 := by simpa using hne
      exact ⟨h, h0⟩
  · exact h

theorem wordsNat_ORDER_TIMES_8 : wordsNat mid.half_size.ORDER_TIMES_8.val = N := by
  unfold mid.half_size.ORDER_TIMES_8
  simp [wordsNat, Nat.ofDigits, N, n25519]

theorem inv_init (K : Nat) (hK : K < 2 ^ 255) (rN rK : U256) (hN : val rN = N) (hk : val rK = K) :
    Inv K { r := rN, t := 0#u128, from_k := false } { r := rK, t := 1#u128, from_k := true } := by
  have h1 : (1#u128 : U128).val = 1 := rfl
  have h0 : (0#u128 : U128).val = 0 := rfl
  have := N_gt
  norm_num at this hK
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr h1⟩ <;> simp only [hN, hk, h0, h1] <;>
    first | omega | simp [Congr, Int.ModEq]

/-- What `split` needs of the row it returns. -/
def Final (K : Nat) (r : U256) (t : U128) (from_k : Bool) : Prop :=
  Congr K (val r) t.val from_k ∧ t.val % 2 = 1 ∧ val r < 2 ^ 255

theorem odd_of_coprime {a b : Nat} (h : Nat.Coprime a b) (hb : b % 2 = 0) : a % 2 = 1 := by
  by_contra ha
  have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (by omega) (by omega)
  rw [h] at h2; omega

@[step]
theorem split_spec (k : Std.Array U64 4#usize) (hk : wordsNat k.val < 2 ^ 255) :
    mid.half_size.split k ⦃ s =>
      (if s.u_negative then -(wordsNat s.u.val : Int) else (wordsNat s.u.val : Int)) ≡
        (wordsNat s.v.val : Int) * wordsNat k.val [ZMOD 8 * n25519] ∧
      wordsNat s.v.val % 2 = 1 ∧ wordsNat s.v.val < 2 ^ 128 ∧ wordsNat s.u.val < 2 ^ 255 ⦄ := by
  unfold mid.half_size.split
  step as ⟨rN, hN⟩
  rw [wordsNat_ORDER_TIMES_8] at hN
  step as ⟨rK, hK⟩
  have hinv := inv_init _ hk rN rK hN hK
  apply WP.spec_bind (split_loop_spec _ _ _ hinv)
  rintro ⟨big, hi, lo, st, sf⟩ ⟨hl, hhi⟩
  simp only at hl hhi ⊢
  set sm : Row := { r := { hi := hi, lo := lo }, t := st, from_k := sf } with hsm
  have hsmall : val sm.r < 2 ^ 128 := by
    have := lo.hBounds; simp only [UScalarTy.numBits] at this
    simp only [hsm, val, hhi]; omega
  simp only [lift, bind_ok]
  apply WP.spec_bind (Pₘ := fun x : U256 × U128 × Bool => Final (wordsNat k.val) x.1 x.2.1 x.2.2)
  · split
    · rename_i hodd
      have hodd' : st.val % 2 = 1 := by
        have := congrArg UScalar.val hodd
        simpa [UScalar.val_and, Nat.and_one_is_mod] using this
      simp only [WP.spec_ok]
      exact ⟨hl.cs, hodd', by have := hsmall; simp only [hsm] at this; omega⟩
    · rename_i heven
      have heven' : st.val % 2 = 0 := by
        have hv : (st &&& 1#u128).val = st.val % 2 := by simp [UScalar.val_and, Nat.and_one_is_mod]
        have : (st &&& 1#u128).val ≠ 1 := fun h' => heven ((UScalar.eq_equiv _ _).mpr (by rw [h']; rfl))
        omega
      have hbodd : big.t.val % 2 = 1 := odd_of_coprime hl.cop heven'
      have hbig : val big.r < 2 ^ 255 := by
        rcases hl.big_lt with h | h
        · exact h
        · simp only [hsm] at h; omega
      have hfin_big : Final (wordsNat k.val) big.r big.t big.from_k := ⟨hl.cb, hbodd, hbig⟩
      have hadd := U128.checked_add_bv_spec st big.t
      split at hadd
      · rename_i z hz
        rw [hz]
        simp only [core.option.Option.map,
          mid.half_size.split.closure.Insts.CoreOpsFunctionFnOnceTupleU128PairU256U128.call_once]
        apply WP.spec_bind (Pₘ := fun diff : Option (U256 × U128) =>
          ∃ d : U256, diff = some (d, z) ∧ val d = val big.r - val sm.r)
        · apply WP.spec_bind (Pₘ := fun m : U256 × U128 => ∃ d : U256, m = (d, z) ∧ val d = val big.r - val sm.r)
          · apply WP.spec_bind (sub_spec big.r sm.r hl.le)
            intro d hd
            simp only [WP.spec_ok]
            exact ⟨d, rfl, hd⟩
          · rintro m ⟨d, rfl, hd⟩
            simp only [WP.spec_ok]
            exact ⟨d, rfl, hd⟩
        rintro diff ⟨d, rfl, hd⟩
        simp only
        have hc := congr_step hl.sign hl.cb hl.cs 0 (by simpa using hl.le)
        simp only [pow_zero, mul_one] at hc
        have hfin_d : Final (wordsNat k.val) d z big.from_k := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hd, hadd.2.1, Nat.add_comm st.val]; exact hc
          · rw [hadd.2.1]; omega
          · rw [hd]; omega
        step*
        split <;> simp_all [WP.spec_ok]
      · rename_i hz
        rw [hz]
        simp only [core.option.Option.map, bind_ok, WP.spec_ok]
        exact hfin_big
  · rintro ⟨r, t, fk⟩ ⟨hc, hodd, hr⟩
    simp only at hc hodd hr
    step as ⟨a, ha⟩
    step*
    have ht := t.hBounds
    simp only [UScalarTy.numBits] at ht
    have hv : wordsNat (Std.Array.make 4#usize [UScalar.cast UScalarTy.U64 t, UScalar.cast UScalarTy.U64 i5,
        0#u64, 0#u64] (by simp)).val = t.val := by
      rw [wordsNat_make4]
      simp only [UScalar.cast_val_eq, UScalarTy.numBits, i5_post, Nat.shiftRight_eq_div_pow]
      have : (0#u64 : U64).val = 0 := rfl
      rw [this]; omega
    rw [hv, ha]
    refine ⟨?_, hodd, ht, hr⟩
    unfold Congr N at hc
    push_cast at hc
    cases fk
    · simp only [Bool.false_eq_true, not_false_eq_true, decide_true, ↓reduceIte] at hc ⊢
      have := hc.neg
      simpa using this
    · simpa using hc

end HalfSize

end rind.x86_64
