import Rind.Aarch64.Asm
import Rind.Poly1305Limbs

open VG VG.AArch64 rind.aarch64.asm rind.spec.poly1305

set_option linter.unusedSimpArgs false

/-!
# Poly1305's block step in rind's copy of aws-lc's aarch64 ChaCha20-Poly1305

aws-lc's seal and open keep the Poly1305 accumulator in three limbs `(x8,
x9, x10)` and `r` in `(x16, x17)`, and `x15` holds 1. Each 16-byte block is
`polyAdd`, which adds it and the bit above it from `(x11, x12)`, then
`polyMul`, which multiplies the accumulator by `r` and reduces it partly,
the 26 instructions of aws-lc's `poly_mul`. `polyMul_ok` runs `polyMul` on
rind's model: it leaves `mulOut` of the accumulator and `r`, which
`limbs_mulOut` shows is `reduce` (`Rind.Poly1305Limbs`) of their product,
for an accumulator below `7 · 2^128` and halves of `r` below `2^60`, as
clamping leaves them; `polyAdd_ok` and `limbs_addT` do the same for the
addition, and `acc_step` combines them into a step of RFC 8439's
accumulator modulo `p`.
-/

namespace rind.aarch64.chacha20poly1305asm

/-- Adds `(x11, x12)` and the bit above it, `x15`, to the accumulator. -/
def polyAdd : List Ins :=
  [.vg (.adds .x .x8 .x8 .x11), .vg (.adcs .x .x9 .x9 .x12), .vg (.adc .x .x10 .x10 .x15)]

/-- Multiplies the accumulator `(x8, x9, x10)` by `r`, `(x16, x17)`, into
four limbs in `(x11, x12, x13, x14)`, and reduces them partly into the
accumulator. -/
def polyMul : List Ins :=
  [.vg (.mul .x .x11 .x8 .x16), .vg (.umulh .x12 .x8 .x16), .vg (.mul .x .x13 .x9 .x16),
   .vg (.umulh .x14 .x9 .x16), .vg (.adds .x .x12 .x12 .x13), .vg (.mul .x .x13 .x10 .x16),
   .vg (.adc .x .x13 .x13 .x14), .vg (.mul .x .x14 .x8 .x17), .vg (.umulh .x8 .x8 .x17),
   .vg (.adds .x .x12 .x12 .x14), .vg (.mul .x .x14 .x9 .x17), .vg (.umulh .x9 .x9 .x17),
   .vg (.adcs .x .x14 .x14 .x8), .vg (.mul .x .x10 .x10 .x17), .vg (.adc .x .x10 .x10 .x9),
   .vg (.adds .x .x13 .x13 .x14), .adcZr .x14 .x10, .andImm .x10 .x13 2 0, .andImm .x8 .x13 62 62,
   .vg (.extr .x .x13 .x14 .x13 2), .vg (.adds .x .x8 .x8 .x11), .vg (.lsr .x .x11 .x14 2),
   .vg (.adc .x .x9 .x14 .x11), .vg (.adds .x .x8 .x8 .x13), .vg (.adcs .x .x9 .x9 .x12),
   .adcZr .x10 .x10]

/-! ## As numbers -/

/-- The product's four limbs `(t0, t1, t2, t3)`, as `polyMul`'s first
seventeen instructions leave them: `r0 · h` in three words, then `r1 · h`
added a word up. -/
def mulT (h0 h1 h2 r0 r1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let a1 := mulHi h0 r0
  let a2 := h1 * r0
  let a3 := mulHi h1 r0
  let b1 := adcV a1 a2 false
  let b2 := adcV (h2 * r0) a3 (carry a1 a2 false)
  let d0 := h0 * r1
  let e0 := mulHi h0 r1
  let t1 := adcV b1 d0 false
  let d1 := h1 * r1
  let f := adcV d1 e0 (carry b1 d0 false)
  let g := adcV (h2 * r1) (mulHi h1 r1) (carry d1 e0 (carry b1 d0 false))
  let t2 := adcV b2 f false
  (h0 * r0, t1, t2, g + BitVec.ofNat 64 (carry b2 f false).toNat)

/-- The accumulator `polyMul` leaves from the product's limbs: the low 130
bits, plus `5 q` for `q` the rest, as `4 q` (`t2` with its low two bits
clear, and `t3` a word up) and `q` added. -/
def reduceT (t : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let (t0, t1, t2, t3) := t
  let lo := t2 &&& Rind.AArch64.bitMask 2 0
  let hm := t2 &&& Rind.AArch64.bitMask 62 62
  let sh := (t3 ++ t2).extractLsb' 2 64
  let u0 := adcV hm t0 false
  let u1 := adcV t3 (t3 >>> 2) (carry hm t0 false)
  (adcV u0 sh false, adcV u1 t1 (carry u0 sh false),
    lo + BitVec.ofNat 64 (carry u1 t1 (carry u0 sh false)).toNat)

/-- What `polyMul` leaves in `(x8, x9, x10)`. -/
def mulOut (h0 h1 h2 r0 r1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  reduceT (mulT h0 h1 h2 r0 r1)

/-- `(h0, h1, h2)` plus the block `(w0, w1)` and `one` above it, as `polyAdd`
leaves it. -/
def addT (h0 h1 h2 w0 w1 one : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  (adcV h0 w0 false, adcV h1 w1 (carry h0 w0 false), adcV h2 one (carry h1 w1 (carry h0 w0 false)))

theorem bitMask3 : Rind.AArch64.bitMask 2 0 = 3#64 := by decide

theorem bitMask_m4 : Rind.AArch64.bitMask 62 62 = ~~~(3#64) := by decide

theorem and3_toNat (x : BitVec 64) : (x &&& Rind.AArch64.bitMask 2 0).toNat = x.toNat % 4 := by
  rw [bitMask3, show (3#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 2 - 1) from rfl, BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.and_two_pow_sub_one_eq_mod]

theorem andm4_eq (x : BitVec 64) : x &&& Rind.AArch64.bitMask 62 62 = (x >>> 2) <<< 2 := by
  rw [show Rind.AArch64.bitMask 62 62 = ~~~(3 : BitVec 64) by decide]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  by_cases h2 : i < 2
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp
  · have h3 : (3 : BitVec 64)[i] = false := by
      rw [← BitVec.getLsbD_eq_getElem, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, BitVec.getLsbD_ofNat]
      simp only [hi, decide_true, Bool.true_and]
      apply Nat.testBit_lt_two_pow
      calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h3, show 2 + (i - 2) = i by omega, BitVec.getLsbD_eq_getElem hi]
    simp [h2]

theorem andm4_toNat (x : BitVec 64) : (x &&& Rind.AArch64.bitMask 62 62).toNat = x.toNat / 4 * 4 := by
  rw [andm4_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega)]

theorem extr_toNat (x y : BitVec 64) : ((y ++ x).extractLsb' 2 64).toNat = x.toNat / 4 + y.toNat % 4 * 2 ^ 62 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem ushr2_toNat (y : BitVec 64) : (y >>> 2).toNat = y.toNat / 4 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! The arithmetic below is over `Nat` variables, each standing for a word's
value, so that `omega` never meets the words themselves, whose values it
would compare by unfolding the sums and carries that make them. -/

theorem mul_nat {P00 P10 P01 P11 Q0 Q1 t0 a1 a2 a3 b1 c1 b2 d0 e0 t1 c2 d1 e1 f c3 g t2 c4 t3 : Nat}
    (hA : a1 * 2 ^ 64 + t0 = P00) (hB : a3 * 2 ^ 64 + a2 = P10) (hD : e0 * 2 ^ 64 + d0 = P01)
    (hF : e1 * 2 ^ 64 + d1 = P11) (bF : e1 < 2 ^ 60) (bG : Q1 ≤ 6 * (2 ^ 60 - 1))
    (s1 : b1 + 2 ^ 64 * c1 = a1 + a2) (s2 : b2 = Q0 + a3 + c1) (s3 : t1 + 2 ^ 64 * c2 = b1 + d0)
    (s4 : f + 2 ^ 64 * c3 = d1 + e0 + c2) (k4 : c3 ≤ 1) (s5 : g = Q1 + e1 + c3)
    (s6 : t2 + 2 ^ 64 * c4 = b2 + f) (k6 : c4 ≤ 1) (s7 : t3 = g + c4) :
    t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 =
      P00 + 2 ^ 64 * (P10 + P01) + 2 ^ 128 * (Q0 + P11) + 2 ^ 192 * Q1 ∧ t3 < 2 ^ 63 := by
  subst hA hB hD hF s2 s5 s7
  constructor <;> omega

theorem small_add (x y c : Nat) (hx : x ≤ 6 * (2 ^ 60 - 1)) (hy : y < 2 ^ 60) (hc : c ≤ 1) :
    x + y + c + 1 < 2 ^ 64 := by omega

theorem reduce_nat {t0 t1 t2 t3 lo hm sh q u0 c5 u1 v0 c6 v1 c7 v2 : Nat}
    (a1 : lo = t2 % 4) (a2 : hm = t2 / 4 * 4) (a3 : sh = t2 / 4 + t3 % 4 * 2 ^ 62) (a4 : q = t3 / 4)
    (s1 : u0 + 2 ^ 64 * c5 = hm + t0) (s2 : u1 = t3 + q + c5) (s3 : v0 + 2 ^ 64 * c6 = u0 + sh)
    (s4 : v1 + 2 ^ 64 * c7 = u1 + t1 + c6) (s5 : v2 = lo + c7) :
    v0 + 2 ^ 64 * v1 + 2 ^ 128 * v2 =
      t0 + 2 ^ 64 * t1 + 2 ^ 128 * (t2 % 4) + 5 * (t2 / 4 + 2 ^ 62 * t3) := by
  subst a1 a2 a3 a4 s2 s5
  omega

/-- The four limbs are the product exactly. -/
theorem mulT_toNat (h0 h1 h2 r0 r1 : BitVec 64) (hh2 : h2.toNat < 7) (hr0 : r0.toNat < 2 ^ 60)
    (hr1 : r1.toNat < 2 ^ 60) :
    (mulT h0 h1 h2 r0 r1).1.toNat + 2 ^ 64 * (mulT h0 h1 h2 r0 r1).2.1.toNat +
        2 ^ 128 * (mulT h0 h1 h2 r0 r1).2.2.1.toNat + 2 ^ 192 * (mulT h0 h1 h2 r0 r1).2.2.2.toNat =
      limbs h0 h1 h2 * (r0.toNat + 2 ^ 64 * r1.toNat) ∧ (mulT h0 h1 h2 r0 r1).2.2.2.toNat < 2 ^ 63 := by
  have e1 : limbs h0 h1 h2 * (r0.toNat + 2 ^ 64 * r1.toNat) =
      h0.toNat * r0.toNat + 2 ^ 64 * (h1.toNat * r0.toNat + h0.toNat * r1.toNat) +
        2 ^ 128 * (h2.toNat * r0.toNat + h1.toNat * r1.toNat) + 2 ^ 192 * (h2.toNat * r1.toNat) := by
    unfold limbs; ring
  rw [e1]
  obtain ⟨eC, bC⟩ := mul_small h2 r0 hh2 hr0
  obtain ⟨eG, bG⟩ := mul_small h2 r1 hh2 hr1
  rw [← eC, ← eG] at *
  have bB := mulHi_lt' h1 r0 hr0; have bF := mulHi_lt' h1 r1 hr1
  simp only [mulT]
  generalize ec1 : carry (mulHi h0 r0) (h1 * r0) false = c1
  have k1 : c1.toNat ≤ 1 := ec1 ▸ carry_le _ _ _
  have s1 := adc_carry (mulHi h0 r0) (h1 * r0) false
  have s2 := adcV_exact (h2 * r0) (mulHi h1 r0) c1 (small_add _ _ 0 bC bB (by omega))
  rw [ec1] at s1
  generalize adcV (mulHi h0 r0) (h1 * r0) false = b1 at s1 ⊢
  generalize adcV (h2 * r0) (mulHi h1 r0) c1 = b2 at s2 ⊢
  generalize ec2 : carry b1 (h0 * r1) false = c2
  have s3 := adc_carry b1 (h0 * r1) false
  rw [ec2] at s3
  generalize ec3 : carry (h1 * r1) (mulHi h0 r1) c2 = c3
  have k3 : c3.toNat ≤ 1 := ec3 ▸ carry_le _ _ _
  have s4 := adc_carry (h1 * r1) (mulHi h0 r1) c2
  rw [ec3] at s4
  have s5 := adcV_exact (h2 * r1) (mulHi h1 r1) c3 (small_add _ _ 0 bG bF (by omega))
  generalize adcV (h1 * r1) (mulHi h0 r1) c2 = f at s4 ⊢
  generalize adcV (h2 * r1) (mulHi h1 r1) c3 = g at s5 ⊢
  generalize adcV b1 (h0 * r1) false = t1 at s3 ⊢
  generalize ec4 : carry b2 f false = c4
  have k4 : c4.toNat ≤ 1 := ec4 ▸ carry_le _ _ _
  have s6 := adc_carry b2 f false
  rw [ec4] at s6
  have s7 := addBit_exact g c4 (by rw [s5]; exact small_add _ _ _ bG bF k3)
  generalize adcV b2 f false = t2 at s6 ⊢
  simp only [Bool.toNat_false, Nat.add_zero] at s1 s3 s6
  exact mul_nat (mul_toNat h0 r0) (mul_toNat h1 r0) (mul_toNat h0 r1) (mul_toNat h1 r1) bF bG
    s1 s2 s3 s4 k3 s5 s6 k4 s7

/-- `polyMul` leaves `reduce` of the accumulator times `r`, exactly. -/
theorem limbs_mulOut (h0 h1 h2 r0 r1 : BitVec 64) (hh2 : h2.toNat < 7) (hr0 : r0.toNat < 2 ^ 60)
    (hr1 : r1.toNat < 2 ^ 60) :
    limbs (mulOut h0 h1 h2 r0 r1).1 (mulOut h0 h1 h2 r0 r1).2.1 (mulOut h0 h1 h2 r0 r1).2.2 =
      reduce (limbs h0 h1 h2 * (r0.toNat + 2 ^ 64 * r1.toNat)) := by
  obtain ⟨ht, h3⟩ := mulT_toNat h0 h1 h2 r0 r1 hh2 hr0 hr1
  rw [← ht]
  revert h3
  simp only [mulOut]
  generalize mulT h0 h1 h2 r0 r1 = t
  obtain ⟨t0, t1, t2, t3⟩ := t
  intro h3
  simp only at h3 ⊢
  rw [reduce_limbs _ _ _ _ t0.isLt t1.isLt]
  simp only [reduceT, limbs]
  have a1 := and3_toNat t2; have a2 := andm4_toNat t2; have a3 := extr_toNat t2 t3
  have a4 := ushr2_toNat t3
  generalize ec5 : carry (t2 &&& Rind.AArch64.bitMask 62 62) t0 false = c5
  have s1 := adc_carry (t2 &&& Rind.AArch64.bitMask 62 62) t0 false
  rw [ec5] at s1
  have k5 : c5.toNat ≤ 1 := ec5 ▸ carry_le _ _ _
  have s2 := adcV_exact t3 (t3 >>> 2) c5 (by rw [a4]; omega)
  generalize (t3 ++ t2).extractLsb' 2 64 = sh at a3 ⊢
  generalize adcV t3 (t3 >>> 2) c5 = u1 at s2 ⊢
  generalize adcV (t2 &&& Rind.AArch64.bitMask 62 62) t0 false = u0 at s1 ⊢
  generalize ec6 : carry u0 sh false = c6
  have s3 := adc_carry u0 sh false
  rw [ec6] at s3
  generalize ec7 : carry u1 t1 c6 = c7
  have s4 := adc_carry u1 t1 c6
  rw [ec7] at s4
  have k7 : c7.toNat ≤ 1 := ec7 ▸ carry_le _ _ _
  have s5 := addBit_exact (t2 &&& Rind.AArch64.bitMask 2 0) c7 (by rw [a1]; omega)
  generalize adcV u0 sh false = v0 at s3 ⊢
  generalize adcV u1 t1 c6 = v1 at s4 ⊢
  simp only [Bool.toNat_false, Nat.add_zero] at s1 s3
  exact reduce_nat a1 a2 a3 a4 s1 s2 s3 s4 s5

/-- An accumulator below `5 · 2^128` plus a block and the one bit above it
is exact, and below `7 · 2^128`. -/
theorem limbs_addT (h0 h1 h2 w0 w1 : BitVec 64) (hh : limbs h0 h1 h2 < 5 * 2 ^ 128) :
    limbs (addT h0 h1 h2 w0 w1 1#64).1 (addT h0 h1 h2 w0 w1 1#64).2.1 (addT h0 h1 h2 w0 w1 1#64).2.2 =
      limbs h0 h1 h2 + w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 ∧ (addT h0 h1 h2 w0 w1 1#64).2.2.toNat < 7 := by
  unfold limbs at hh ⊢
  simp only [addT]
  have l0 := h0.isLt; have l1 := h1.isLt
  generalize ec1 : carry h0 w0 false = c1
  have s1 := adc_carry h0 w0 false
  rw [ec1] at s1
  generalize ec2 : carry h1 w1 c1 = c2
  have s2 := adc_carry h1 w1 c1
  rw [ec2] at s2
  have k2 : c2.toNat ≤ 1 := ec2 ▸ carry_le _ _ _
  have e1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have s3 := adcV_exact h2 1#64 c2 (by rw [e1]; omega)
  rw [e1] at s3
  rw [s3]
  generalize adcV h0 w0 false = v0 at s1 ⊢
  generalize adcV h1 w1 c1 = v1 at s2 ⊢
  simp only [Bool.toNat_false, Nat.add_zero] at s1
  generalize h0.toNat = n0 at *
  generalize h1.toNat = n1 at *
  generalize h2.toNat = n2 at *
  generalize v0.toNat = m0 at *
  generalize v1.toNat = m1 at *
  generalize w0.toNat = x0 at *
  generalize w1.toNat = x1 at *
  generalize c1.toNat = d1 at *
  generalize c2.toNat = d2 at *
  constructor <;> omega

/-- A block added to an accumulator below `5 · 2^128`, then times `r`: below
`5 · 2^128` again, and the next accumulator modulo `p`. -/
theorem acc_step (h0 h1 h2 w0 w1 r0 r1 : BitVec 64) (a m : Nat) (hr0 : r0.toNat < 2 ^ 60)
    (hr1 : r1.toNat < 2 ^ 60) (hlt : limbs h0 h1 h2 < 5 * 2 ^ 128) (ha : limbs h0 h1 h2 % p = a % p)
    (hm : w0.toNat + 2 ^ 64 * w1.toNat = m) :
    let o := addT h0 h1 h2 w0 w1 1#64
    let o' := mulOut o.1 o.2.1 o.2.2 r0 r1
    limbs o'.1 o'.2.1 o'.2.2 < 5 * 2 ^ 128 ∧
      limbs o'.1 o'.2.1 o'.2.2 % p = (a + m + 2 ^ 128) * (r0.toNat + 2 ^ 64 * r1.toNat) % p := by
  intro o o'
  obtain ⟨e1, b1⟩ := limbs_addT h0 h1 h2 w0 w1 hlt
  rw [show limbs o'.1 o'.2.1 o'.2.2 = _ from limbs_mulOut o.1 o.2.1 o.2.2 r0 r1 b1 hr0 hr1]
  have e3 : limbs o.1 o.2.1 o.2.2 = limbs h0 h1 h2 + m + 2 ^ 128 := by rw [e1, ← hm]; ring
  rw [e3]
  have hr : r0.toNat + 2 ^ 64 * r1.toNat < 2 ^ 124 := by omega
  exact ⟨reduce_lt (by omega) hr, reduce_step _ _ _ _ ha⟩

/-! ## The blocks on rind's model -/

/-- The accumulator `(x8, x9, x10)` and `r`, `(x16, x17)`, of a state. -/
abbrev acc (s : S) : BitVec 64 × BitVec 64 × BitVec 64 := (s.vg.gpr .x8, s.vg.gpr .x9, s.vg.gpr .x10)

/-- `polyMul` leaves `mulOut` of the accumulator and `r`. -/
theorem polyMul_ok (s : S) :
    let o := mulOut (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) (s.vg.gpr .x16) (s.vg.gpr .x17)
    ∃ s', execBlock I polyMul s = some (s', []) ∧
      s'.vg.gpr .x8 = o.1 ∧ s'.vg.gpr .x9 = o.2.1 ∧ s'.vg.gpr .x10 = o.2.2 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [] [.x8, .x9, .x10, .x11, .x12, .x13, .x14] := by
  intro o
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [polyMul]
    rfl
  · rfl
  · a64_out

/-- `polyAdd` leaves `addT` of the accumulator, `(x11, x12)`, and `x15`. -/
theorem polyAdd_ok (s : S) :
    let o := addT (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) (s.vg.gpr .x11) (s.vg.gpr .x12)
      (s.vg.gpr .x15)
    ∃ s', execBlock I polyAdd s = some (s', []) ∧
      s'.vg.gpr .x8 = o.1 ∧ s'.vg.gpr .x9 = o.2.1 ∧ s'.vg.gpr .x10 = o.2.2 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [] [.x8, .x9, .x10] := by
  intro o
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [polyAdd]
    rfl
  · rfl
  · a64_out

end rind.aarch64.chacha20poly1305asm

/-- info: 'rind.aarch64.chacha20poly1305asm.acc_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.aarch64.chacha20poly1305asm.acc_step

/-- info: 'rind.aarch64.chacha20poly1305asm.polyMul_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.aarch64.chacha20poly1305asm.polyMul_ok
