import Rind.X86_64.Asm
import Rind.Poly1305Limbs

open VG VG.X86_64 rind.x86_64.asm rind.spec.poly1305

/-!
# aws-lc's `poly_mul` on x86_64, as numbers

`mulOut` is what the block `PolyHashAd.mul` leaves in the accumulator's three
limbs, as rind's x86_64 model computes it, step by step; `limbs_mulOut`
shows it is `reduce` of the accumulator times `r` (`Rind.Poly1305Limbs`),
exactly, for an accumulator below `7 · 2^128` and halves of `r` below
`2^60`, as clamping leaves them.
-/

namespace rind.x86_64.polyhashad

/-- The carry out of `a + b + c`. -/
def carry3 (a b : BitVec 64) (c : Bool) : Bool := decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)

/-- `adc`'s sum. -/
abbrev adcV (a b : BitVec 64) (c : Bool) : BitVec 64 := a + b + (BitVec.ofBool c).setWidth 64

/-- The product's four limbs, `(t0, t1, t2, t3)`: the low words of `r0 · h`
in `r13`, `r14`, and `r15`, then `r1 · h` added a word up, into `r9` too. -/
def mulT (h0 h1 h2 r0 r1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let t1a := mulHi r0 h0 + mulLo r0 h1
  let t2a := adcV (r0 * h2) (mulHi r0 h1) (carry (mulHi r0 h0) (mulLo r0 h1))
  let t1 := t1a + mulLo r1 h0
  let e := mulHi r1 h0 + (BitVec.ofBool (carry t1a (mulLo r1 h0))).setWidth 64
  let t2b := t2a + mulLo r1 h1
  let f := mulHi r1 h1 + (BitVec.ofBool (carry t2a (mulLo r1 h1))).setWidth 64
  let t2 := t2b + e
  let t3 := adcV (r1 * h2) f (carry t2b e)
  (mulLo r0 h0, t1, t2, t3)

/-- The accumulator `mul` leaves from the product's limbs: the low 130 bits,
plus `5 q` for `q` the rest, as `q`'s two words `4 q` and `q` added. -/
def reduceT (t : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let (t0, t1, t2, t3) := t
  let lo := t2 &&& (3 : BitVec 32).signExtend 64
  let hm := t2 &&& (-4 : BitVec 32).signExtend 64
  let sh := (t2 >>> 2) ||| (t3 <<< 62)
  let q0 := sh + hm
  let q1 := adcV (t3 >>> 2) t3 (carry sh hm)
  (t0 + q0, adcV t1 q1 (carry t0 q0), lo + (BitVec.ofBool (carry3 t1 q1 (carry t0 q0))).setWidth 64)

/-- What `mul` leaves in `(r10, r11, r12)`. -/
def mulOut (h0 h1 h2 r0 r1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  reduceT (mulT h0 h1 h2 r0 r1)

/-- `(h0, h1, h2)` plus the block `(w0, w1)` and the one bit above it:
`add`, `adc`, and `adc $1`. -/
def addT (h0 h1 h2 w0 w1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  (h0 + w0, adcV h1 w1 (carry h0 w0), adcV h2 1#64 (carry3 h1 w1 (carry h0 w0)))

/-- `(r13, r14)` a byte up, the byte `x` below it: `shld`, `shl`, and `xor` of
the byte zero-extended. -/
def tailStep (a b : BitVec 64) (x : BitVec 8) : BitVec 64 × BitVec 64 :=
  ((a <<< 8) ^^^ x.setWidth 64, (b <<< 8) ||| (a >>> 56))

/-! ## As numbers -/

theorem carry_toNat (a b : BitVec 64) : (carry a b).toNat = (a.toNat + b.toNat) / 2 ^ 64 := by
  have := a.isLt; have := b.isLt
  unfold carry
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat
  · rw [decide_eq_true h, Bool.toNat_true]; omega
  · rw [decide_eq_false h, Bool.toNat_false]; omega

theorem carry3_toNat (a b : BitVec 64) (c : Bool) :
    (carry3 a b c).toNat = (a.toNat + b.toNat + c.toNat) / 2 ^ 64 := by
  have := a.isLt; have := b.isLt; have : c.toNat ≤ 1 := Bool.toNat_le c
  unfold carry3
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · rw [decide_eq_true h, Bool.toNat_true]; omega
  · rw [decide_eq_false h, Bool.toNat_false]; omega

theorem add_toNat (a b : BitVec 64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b

theorem adcV_toNat (a b : BitVec 64) (c : Bool) :
    (adcV a b c).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
  simp only [adcV, BitVec.toNat_add, ofBool_toNat]
  omega

theorem and3_toNat (x : BitVec 64) : (x &&& (3 : BitVec 32).signExtend 64).toNat = x.toNat % 4 := by
  rw [show (3 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (2 ^ 2 - 1) by decide, BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.and_two_pow_sub_one_eq_mod]

theorem andm4_eq (x : BitVec 64) : x &&& (-4 : BitVec 32).signExtend 64 = (x >>> 2) <<< 2 := by
  rw [show (-4 : BitVec 32).signExtend 64 = ~~~(3 : BitVec 64) by decide]
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

theorem andm4_toNat (x : BitVec 64) : (x &&& (-4 : BitVec 32).signExtend 64).toNat = x.toNat / 4 * 4 := by
  rw [andm4_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega)]

theorem shrd_toNat (x y : BitVec 64) : ((x >>> 2) ||| (y <<< 62)).toNat = x.toNat / 4 + y.toNat % 4 * 2 ^ 62 := by
  have hz : (x >>> 2) &&& (y <<< 62) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    by_cases h : i < 62
    · simp [h]
    · have : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
      simp [this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have := x.isLt
  omega

theorem ushr2_toNat (y : BitVec 64) : (y >>> 2).toNat = y.toNat / 4 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A product of words below `2^60` and `2^64`, in its high word: below `2^60`. -/
theorem mulHi_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 60) : (mulHi a b).toNat < 2 ^ 60 := by
  have h := mul_toNat a b
  have : a.toNat * b.toNat < 2 ^ 60 * 2 ^ 64 :=
    Nat.mul_lt_mul_of_lt_of_le ha b.isLt.le (by norm_num)
  have := (mulLo a b).isLt
  omega

theorem mul_small (a b : BitVec 64) (ha : a.toNat < 2 ^ 60) (hb : b.toNat < 7) :
    (a * b).toNat = a.toNat * b.toNat ∧ a.toNat * b.toNat ≤ (2 ^ 60 - 1) * 6 := by
  have : a.toNat * b.toNat ≤ (2 ^ 60 - 1) * 6 := Nat.mul_le_mul (by omega) (by omega)
  exact ⟨by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)], this⟩

theorem add_carry (a b : BitVec 64) : (a + b).toNat + 2 ^ 64 * (carry a b).toNat = a.toNat + b.toNat := by
  rw [carry_toNat, BitVec.toNat_add]; omega

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (adcV a b c).toNat + 2 ^ 64 * (carry3 a b c).toNat = a.toNat + b.toNat + c.toNat := by
  rw [carry3_toNat, adcV_toNat]; omega

theorem adcV_exact (a b : BitVec 64) (c : Bool) (h : a.toNat + b.toNat + 1 < 2 ^ 64) :
    (adcV a b c).toNat = a.toNat + b.toNat + c.toNat := by
  have := Bool.toNat_le c
  rw [adcV_toNat, Nat.mod_eq_of_lt (by omega)]

theorem addBit_exact (a : BitVec 64) (c : Bool) (h : a.toNat + 1 < 2 ^ 64) :
    (a + (BitVec.ofBool c).setWidth 64).toNat = a.toNat + c.toNat := by
  have := Bool.toNat_le c
  rw [BitVec.toNat_add, ofBool_toNat, Nat.mod_eq_of_lt (by omega)]

theorem carry_le (a b : BitVec 64) : (carry a b).toNat ≤ 1 := Bool.toNat_le _

/-- The four limbs are the product exactly. -/
theorem mulT_toNat (h0 h1 h2 r0 r1 : BitVec 64) (hh2 : h2.toNat < 7) (hr0 : r0.toNat < 2 ^ 60)
    (hr1 : r1.toNat < 2 ^ 60) :
    let t := mulT h0 h1 h2 r0 r1
    t.1.toNat + 2 ^ 64 * t.2.1.toNat + 2 ^ 128 * t.2.2.1.toNat + 2 ^ 192 * t.2.2.2.toNat =
      limbs h0 h1 h2 * (r0.toNat + 2 ^ 64 * r1.toNat) ∧ t.2.2.2.toNat < 2 ^ 63 := by
  intro t
  have e1 : (h0.toNat + 2 ^ 64 * h1.toNat + 2 ^ 128 * h2.toNat) * (r0.toNat + 2 ^ 64 * r1.toNat) =
      r0.toNat * h0.toNat + 2 ^ 64 * (r0.toNat * h1.toNat + r1.toNat * h0.toNat) +
        2 ^ 128 * (r0.toNat * h2.toNat + r1.toNat * h1.toNat) + 2 ^ 192 * (r1.toNat * h2.toNat) := by ring
  simp only [t, mulT, limbs, e1]
  obtain ⟨eC, bC⟩ := mul_small r0 h2 hr0 hh2
  obtain ⟨eG, bG⟩ := mul_small r1 h2 hr1 hh2
  have hA := mul_toNat r0 h0; have hB := mul_toNat r0 h1
  have hD := mul_toNat r1 h0; have hF := mul_toNat r1 h1
  have bB := mulHi_lt r0 h1 hr0; have bD := mulHi_lt r1 h0 hr1; have bF := mulHi_lt r1 h1 hr1
  -- `r0 · h` in three limbs.
  have s1 := add_carry (mulHi r0 h0) (mulLo r0 h1)
  have k1 := carry_le (mulHi r0 h0) (mulLo r0 h1)
  have s2 := adcV_exact (r0 * h2) (mulHi r0 h1) (carry (mulHi r0 h0) (mulLo r0 h1)) (by omega)
  generalize mulHi r0 h0 + mulLo r0 h1 = t1a at s1 ⊢
  generalize adcV (r0 * h2) (mulHi r0 h1) (carry (mulHi r0 h0) (mulLo r0 h1)) = t2a at s2 ⊢
  generalize carry (mulHi r0 h0) (mulLo r0 h1) = c1 at s1 k1 s2
  -- `r1 · h0` a word up.
  have s3 := add_carry t1a (mulLo r1 h0)
  have k3 := carry_le t1a (mulLo r1 h0)
  have s4 := addBit_exact (mulHi r1 h0) (carry t1a (mulLo r1 h0)) (by omega)
  generalize mulHi r1 h0 + (BitVec.ofBool (carry t1a (mulLo r1 h0))).setWidth 64 = e at s4 ⊢
  generalize carry t1a (mulLo r1 h0) = c3 at s3 k3 s4
  -- `r1 · h1` two words up.
  have s5 := add_carry t2a (mulLo r1 h1)
  have k5 := carry_le t2a (mulLo r1 h1)
  have s6 := addBit_exact (mulHi r1 h1) (carry t2a (mulLo r1 h1)) (by omega)
  generalize mulHi r1 h1 + (BitVec.ofBool (carry t2a (mulLo r1 h1))).setWidth 64 = f at s6 ⊢
  generalize carry t2a (mulLo r1 h1) = c5 at s5 k5 s6
  have s7 := add_carry (t2a + mulLo r1 h1) e
  have k7 := carry_le (t2a + mulLo r1 h1) e
  have s8 := adcV_exact (r1 * h2) f (carry (t2a + mulLo r1 h1) e) (by omega)
  generalize adcV (r1 * h2) f (carry (t2a + mulLo r1 h1) e) = t3 at s8 ⊢
  generalize carry (t2a + mulLo r1 h1) e = c7 at s7 k7 s8
  constructor <;> omega

theorem limbs_mulOut (h0 h1 h2 r0 r1 : BitVec 64) (hh2 : h2.toNat < 7) (hr0 : r0.toNat < 2 ^ 60)
    (hr1 : r1.toNat < 2 ^ 60) :
    let o := mulOut h0 h1 h2 r0 r1
    limbs o.1 o.2.1 o.2.2 = reduce (limbs h0 h1 h2 * (r0.toNat + 2 ^ 64 * r1.toNat)) := by
  intro o
  obtain ⟨ht, h3⟩ := mulT_toNat h0 h1 h2 r0 r1 hh2 hr0 hr1
  rw [← ht]
  revert h3
  simp only [o, mulOut]
  generalize mulT h0 h1 h2 r0 r1 = t
  obtain ⟨t0, t1, t2, t3⟩ := t
  intro h3
  simp only at h3 ⊢
  rw [reduce_limbs _ _ _ _ t0.isLt t1.isLt]
  simp only [reduceT, limbs]
  have a1 := and3_toNat t2; have a2 := andm4_toNat t2; have a3 := shrd_toNat t2 t3
  have a4 := ushr2_toNat t3
  have s1 := add_carry ((t2 >>> 2) ||| (t3 <<< 62)) (t2 &&& (-4 : BitVec 32).signExtend 64)
  have k1 := carry_le ((t2 >>> 2) ||| (t3 <<< 62)) (t2 &&& (-4 : BitVec 32).signExtend 64)
  have s2 := adcV_exact (t3 >>> 2) t3 (carry ((t2 >>> 2) ||| (t3 <<< 62)) (t2 &&& (-4 : BitVec 32).signExtend 64))
    (by omega)
  generalize (t2 >>> 2) ||| (t3 <<< 62) = sh at a3 s1 k1 s2 ⊢
  generalize t2 &&& (-4 : BitVec 32).signExtend 64 = hm at a2 s1 k1 s2 ⊢
  generalize adcV (t3 >>> 2) t3 (carry sh hm) = q1 at s2 ⊢
  generalize sh + hm = q0 at s1 ⊢
  have s3 := add_carry t0 q0
  have s4 := adc_carry t1 q1 (carry t0 q0)
  have k4 := Bool.toNat_le (carry3 t1 q1 (carry t0 q0))
  have s5 := addBit_exact (t2 &&& (3 : BitVec 32).signExtend 64) (carry3 t1 q1 (carry t0 q0)) (by omega)
  rw [s5]
  omega

/-- An accumulator below `5 · 2^128` plus a block and the one bit above it
is exact, and below `7 · 2^128`. -/
theorem limbs_addT (h0 h1 h2 w0 w1 : BitVec 64) (hh : limbs h0 h1 h2 < 5 * 2 ^ 128) :
    let o := addT h0 h1 h2 w0 w1
    limbs o.1 o.2.1 o.2.2 = limbs h0 h1 h2 + w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 ∧ o.2.2.toNat < 7 := by
  intro o
  unfold limbs at hh
  have s1 := add_carry h0 w0
  have k1 := carry_le h0 w0
  have s2 := adc_carry h1 w1 (carry h0 w0)
  have k2 := Bool.toNat_le (carry3 h1 w1 (carry h0 w0))
  have e1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have s3 := adcV_exact h2 1#64 (carry3 h1 w1 (carry h0 w0)) (by rw [e1]; omega)
  rw [e1] at s3
  simp only [o, addT, limbs, s3]
  have := h0.isLt; have := h1.isLt
  constructor <;> omega

/-- Below `2^56`, the low word's bits above 56 shifted in, `(r13, r14)` a
byte up is the number times 256 plus the byte. -/
theorem tailStep_toNat (a b : BitVec 64) (x : BitVec 8) (h : b.toNat * 2 ^ 64 + a.toNat < 2 ^ 120) :
    let o := tailStep a b x
    o.2.toNat * 2 ^ 64 + o.1.toNat = (b.toNat * 2 ^ 64 + a.toNat) * 256 + x.toNat := by
  intro o
  have hx : ((a <<< 8) ^^^ x.setWidth 64).toNat = a.toNat * 256 % 2 ^ 64 + x.toNat := by
    have hz : (a <<< 8) &&& x.setWidth 64 = 0#64 := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getElem_zero]
      by_cases h8 : i < 8
      · simp [h8]
      · simp [h8, BitVec.getLsbD_of_ge x i (by omega)]
    have ho : (a <<< 8) ^^^ x.setWidth 64 = (a <<< 8) ||| x.setWidth 64 := by
      ext i hi
      have := congrArg (·[i]) hz
      simp only [BitVec.getElem_and, BitVec.getElem_zero] at this
      simp only [BitVec.getElem_xor, BitVec.getElem_or]
      revert this
      cases (a <<< 8)[i] <;> cases (x.setWidth 64)[i] <;> simp
    rw [ho, ← BitVec.add_eq_or_of_and_eq_zero _ _ hz, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    have := x.isLt
    have : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt (by omega)
    omega
  have hb : ((b <<< 8) ||| (a >>> 56)).toNat = b.toNat * 256 + a.toNat / 2 ^ 56 := by
    have hz : (b <<< 8) &&& (a >>> 56) = 0#64 := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, BitVec.getElem_zero]
      by_cases h8 : i < 8
      · simp [h8]
      · simp [h8, BitVec.getLsbD_of_ge a (56 + i) (by omega)]
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have := a.isLt
    omega
  simp only [o, tailStep, hx, hb]
  have := a.isLt
  omega

end rind.x86_64.polyhashad
