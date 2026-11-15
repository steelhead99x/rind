import Rind.X86_64.Funs
import Rind.RsaLemmas
import Mathlib.Tactic.Ring
open Aeneas Aeneas.Std Result rind.spec

/-!
# The non-adjacent form, `mid::util::public_naf`

`naf_spec` proves that `public_naf::<W>`, for a width of 5 or 6, writes the
width-`W` NAF of a scalar of `L` 64-bit words into `64L + 1` digits: digits
that name the scalar, each zero or odd and below 2^(W-1) in magnitude. P-256's
and P-384's ECDSA verification read them. `admin/prove` writes the aarch64
proof from this file by renaming the target.
-/

namespace rind.x86_64

namespace Naf

private theorem getElem_eq_getElem! {α : Type _} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i] = l[i]! := by
  simp [getElem!_pos l i h]

/-- The integer that little-endian signed digits name: d₀ + 2d₁ + 4d₂ + ⋯. -/
def nafVal : List I8 → Int
  | [] => 0
  | d :: ds => d.val + 2 * nafVal ds

theorem nafVal_append (l1 l2 : List I8) : nafVal (l1 ++ l2) = nafVal l1 + 2 ^ l1.length * nafVal l2 := by
  induction l1 with
  | nil => simp [nafVal]
  | cons d ds ih => simp only [List.cons_append, nafVal, ih, List.length_cons, pow_succ]; ring

theorem nafVal_drop (l : List I8) (i : Nat) (hi : i < l.length) :
    nafVal (l.drop i) = (l[i]!).val + 2 * nafVal (l.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, nafVal, getElem_eq_getElem! _ _ hi]

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

/-- Bit `i` of a number's limbs is bit `i % 64` of limb `i / 64`, or zero
above them. -/
theorem wordsNat_bit : ∀ (l : List U64) (i : Nat),
    wordsNat l / 2 ^ i % 2 = if i / 64 < l.length then (l[i / 64]!).val / 2 ^ (i % 64) % 2 else 0
  | [], i => by simp [wordsNat]
  | x :: xs, i => by
    rw [rind.spec.rsa.wordsNat_cons]
    have hx := x.hBounds
    simp only [UScalarTy.numBits] at hx
    by_cases hi : i < 64
    · rw [div_split_lo _ _ _ hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = 64 + j := ⟨i - 64, by omega⟩
      rw [div_split_hi _ _ _ hx, wordsNat_bit xs j,
        show (64 + j) / 64 = j / 64 + 1 by omega, show (64 + j) % 64 = j % 64 by omega]
      simp

/-- The low `w` bits of a number's limbs are its first limb's. -/
theorem wordsNat_mod (l : List U64) (hl : 0 < l.length) (w : Nat) (hw : w ≤ 64) :
    wordsNat l % 2 ^ w = (l[0]!).val % 2 ^ w := by
  match l, hl with
  | x :: xs, _ =>
    rw [rind.spec.rsa.wordsNat_cons]
    have h : 2 ^ 64 = 2 ^ w * 2 ^ (64 - w) := by rw [← Nat.pow_add]; congr 1; omega
    rw [h, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    simp

@[step]
theorem bit_spec (k : Slice U64) (i : Usize) :
    mid.util.bit k i ⦃ r => r.val = ((wordsNat k.val / 2 ^ i.val % 2 : Nat) : Int) ⦄ := by
  unfold mid.util.bit Shared0U64.Insts.CoreOpsBitShrUsizeU64.shr
  rw [wordsNat_bit]
  step as ⟨i1, hi1⟩
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok, Slice.getElem?_Usize_eq, hi1]
  by_cases hq : i.val / 64 < k.val.length
  · rw [ite_eq_left_iff.mpr (fun h => absurd hq h), List.getElem?_eq_getElem hq]
    simp only
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3, _⟩
    step as ⟨i4, hi4, _⟩
    simp only [UScalar.hcast_val_eq]
    rw [hi4, UScalar.val_and, hi3, hi2, Nat.shiftRight_eq_div_pow, show (1#u64 : U64).val = 1 from rfl,
      Nat.and_one_is_mod, getElem_eq_getElem! _ _ hq]
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

theorem M_facts (B i w : Nat) (hw : w = 5 ∨ w = 6) (hi : i < B + 1) :
    ((∃ t, ((2 ^ B / 2 ^ i : Nat) : Int) = 2 * 2 ^ (w - 1) * t) ∨
        ((2 ^ B / 2 ^ i : Nat) : Int) ≤ 2 ^ (w - 1)) ∧
      (((2 ^ B / 2 ^ i : Nat) : Int) % 2 = 0 ∨ ((2 ^ B / 2 ^ i : Nat) : Int) ≤ 1) ∧
      ((2 ^ B / 2 ^ i : Nat) : Int) / 2 = ((2 ^ B / 2 ^ (i + 1) : Nat) : Int) := by
  have hpow : 2 ^ B / 2 ^ i = 2 ^ (B - i) := Nat.pow_div (by omega) (by norm_num)
  have hpow1 : 2 ^ B / 2 ^ (i + 1) = 2 ^ B / 2 ^ i / 2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  rw [hpow1, hpow]
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : w ≤ B - i
    · left
      refine ⟨2 ^ (B - i - w), ?_⟩
      push_cast
      rw [← pow_succ', ← pow_add]
      congr 1; omega
    · right
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
  · by_cases h : B - i = 0
    · right; rw [h]; norm_num
    · left; push_cast
      rw [show B - i = (B - i - 1) + 1 by omega, pow_succ]; simp
  · push_cast
    norm_cast

/-- The NAF loop's state after `s` of `B + 1` digits, for a number below
2^B: the digits so far name `K` but for the remainder `w` +
2^W·⌊K / 2^(s+W)⌋ times 2^s, which is at most 2^(B-s). -/
def nafInv (B w : Nat) (K : Nat) (s : Nat) (digits : List I8) (window : Int) : Prop :=
  digits.length = B + 1 ∧ 0 ≤ window ∧ window ≤ 2 * 2 ^ (w - 1) ∧
    (K : Int) = nafVal (digits.take s) + 2 ^ s * (window + 2 * 2 ^ (w - 1) * ((K / 2 ^ (s + w) : Nat) : Int)) ∧
    window + 2 * 2 ^ (w - 1) * ((K / 2 ^ (s + w) : Nat) : Int) ≤ ((2 ^ B / 2 ^ s : Nat) : Int) ∧
    ∀ j < s, nafDigit (2 ^ (w - 1)) (digits[j]!).val

theorem nafVal_take_succ (l : List I8) (i : Nat) (hi : i < l.length) (d : I8) :
    nafVal ((l.set i d).take (i + 1)) = nafVal (l.take i) + 2 ^ i * d.val := by
  rw [List.take_add_one, List.getElem?_set_self hi, List.take_set_of_le (by omega), nafVal_append,
    List.length_take, Nat.min_eq_left (by omega)]
  simp [nafVal]

theorem naf_inv_step (B w K i : Nat) (hw : w = 5 ∨ w = 6) (hi : i < B + 1) (ds : List I8) (win : Int)
    (hinv : nafInv B w K i ds win) (dd : I8)
    (hdd : dd.val = if win % 2 = 1 then (if win < 2 ^ (w - 1) then win else win - 2 * 2 ^ (w - 1)) else 0) :
    nafInv B w K (i + 1) (ds.set i dd)
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
  obtain ⟨hM1, hM2, hM3⟩ := M_facts B i w hw hi
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

set_option maxHeartbeats 1000000 in
theorem naf_loop_spec (W : U32) (hW : W.val = 5 ∨ W.val = 6) (k : Slice U64) (B : Nat)
    (hk : 64 * k.length = B) (hB : B < 2 ^ 16) (iter : core.ops.range.Range Usize) (digits : Slice I8) (window : I32)
    (he : iter.end.val = B + 1) (hs : iter.start.val ≤ B + 1)
    (hinv : nafInv B W.val (wordsNat k.val) iter.start.val digits.val window.val) :
    mid.util.public_naf_loop W iter k digits window ⦃ r =>
      r.length = B + 1 ∧ nafVal r.val = wordsNat k.val ∧
        ∀ j < B + 1, nafDigit (2 ^ (W.val - 1)) (r.val[j]!).val ⦄ := by
  unfold mid.util.public_naf_loop
  apply loop.spec_decr_nat (fun x => B + 1 - x.1.start.val)
    (fun x => x.1.end.val = B + 1 ∧ x.1.start.val ≤ B + 1 ∧
      nafInv B W.val (wordsNat k.val) x.1.start.val x.2.1.val x.2.2.val)
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
        have hnew := naf_inv_step B W.val (wordsNat k.val) it.start.val hW (by omega) ds.val win.val
          ⟨hlen, hw0, hw, hsum, hbound, hdig⟩ dd hdd
        have hw1r : 0 ≤ w1.val ∧ w1.val ≤ 2 * 2 ^ (W.val - 1) := by
          rw [hw1, hdd]; rcases hA with h | h <;> rw [h] <;> split_ifs <;> omega
        step as ⟨i2, hi2, _⟩
        step as ⟨i3, hi3⟩
        have hi3v : i3.val = W.val := by
          rw [hi3, UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
        step as ⟨i4, hi4⟩
        · rw [hi3v]; have hB' : B < 65536 := hB
          rcases Usize.bounds_eq with h | h <;> rw [h] <;> norm_num [U32.max, U64.max, U32.numBits, U64.numBits] <;> omega
        step with bit_spec k i4 as ⟨i5, hi5⟩
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
      have hB : it.start.val = B + 1 := by omega
      rw [hB] at hsum hbound hdig
      have hz : (2 ^ B / 2 ^ (B + 1) : Nat) = 0 := Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [hz] at hbound
      have hK : wordsNat k.val / 2 ^ (B + 1 + W.val) = 0 := Nat.div_eq_of_lt (by
        calc wordsNat k.val < 2 ^ B := by
              have := rind.spec.rsa.wordsNat_lt' k.val
              rwa [show 64 * k.val.length = B from hk] at this
          _ ≤ 2 ^ (B + 1 + W.val) := Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hK] at hsum hbound
      refine ⟨hlen, ?_, hdig⟩
      have hwz : win.val = 0 := by push_cast at hbound; omega
      rw [hwz] at hsum
      rw [List.take_of_length_le (by rw [hlen])] at hsum
      simp at hsum; omega
  · exact ⟨he, hs, hinv⟩

/-- `public_naf::<W>` writes the width-`W` NAF of `k`, `B` = 64 times its
length bits, into `B + 1` digits. -/
theorem naf_spec (W : U32) (hW : W.val = 5 ∨ W.val = 6) (k : Slice U64) (B : Nat)
    (hk : 64 * k.length = B) (hB : B < 2 ^ 16) (hk0 : 0 < k.length) (digits : Slice I8) (hd : digits.length = B + 1) :
    mid.util.public_naf W k digits ⦃ r =>
      r.length = B + 1 ∧ nafVal r.val = wordsNat k.val ∧
        ∀ j < B + 1, nafDigit (2 ^ (W.val - 1)) (r.val[j]!).val ⦄ := by
  unfold mid.util.public_naf
  have hkl : 0 < k.val.length := hk0
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
  have hK : wordsNat k.val < 2 ^ B := by
    have := rind.spec.rsa.wordsNat_lt' k.val
    rwa [show 64 * k.val.length = B from hk] at this
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
  apply naf_loop_spec W hW k B hk hB _ digits win (by simp [Slice.len, hd]) (by simp)
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
    exact_mod_cast (show wordsNat k.val % 2 ^ W.val + 2 ^ W.val * (wordsNat k.val / 2 ^ W.val) ≤ 2 ^ B by
      rw [Nat.mod_add_div]; omega)

end Naf

end rind.x86_64
