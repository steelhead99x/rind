import Rind.X86_64.Mul4xModel

open rind.x86_64.asm rind.x86_64.mul4x

set_option exponentiation.threshold 512

/-!
# `bn_mulx4x_mont`'s arithmetic

The words a block of aws-lc's `bn_mulx4x_mont` computes, as its `mulx`,
`adcx`, and `adox` compute them, and what they add up to. A block runs two
carry chains: the `a·b` chain (`adcx` alone in the first pass; `adox` for
`a·b` and `adcx` for `t` in the others), then the `q·n` chain (`adox` for the
high words, `adcx` for the low ones). Each chain ends in a register that
cannot overflow, since its high word `mulx`'s is at most `2^64 - 2`, and every
carry the block drops is zero because the block's sum is below `2^320`.
-/

namespace rind.x86_64.mulx4x

/-- `x + y + c` and its carry out, as `adcx`, `adox`, and `adc` leave them. -/
def adc (x y : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  (x + y + (BitVec.ofBool c).setWidth 64, decide (2 ^ 64 ≤ x.toNat + y.toNat + c.toNat))

/-- `adc` of the zero register `rbp`, in the form running the instruction leaves. -/
def adc0 (x : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  (x + (BitVec.ofBool c).setWidth 64, decide (2 ^ 64 ≤ x.toNat + (0 : BitVec 64).toNat + c.toNat))

theorem adc_nat (x y : BitVec 64) (c : Bool) :
    (adc x y c).1.toNat + 2 ^ 64 * (adc x y c).2.toNat = x.toNat + y.toNat + c.toNat := by
  have := x.isLt; have := y.isLt; have := Bool.toNat_le c
  simp only [adc, BitVec.toNat_add, ofBool_toNat]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + c.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

theorem adc0_nat (x : BitVec 64) (c : Bool) :
    (adc0 x c).1.toNat + 2 ^ 64 * (adc0 x c).2.toNat = x.toNat + c.toNat := by
  have h := adc_nat x 0 c
  simpa [adc, adc0] using h

theorem mulHi_le (a b : BitVec 64) : (mulHi a b).toNat ≤ 2 ^ 64 - 2 := by
  have h1 := mul_toNat a b; have h2 := mul_le a b; have := (mulLo a b).isLt
  omega

/-- The value of four words, least significant first. -/
def v4 (w0 w1 w2 w3 : BitVec 64) : Nat := w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat

theorem v4_lt (w0 w1 w2 w3 : BitVec 64) : v4 w0 w1 w2 w3 < 2 ^ 256 := by
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  unfold v4; omega

theorem mul_v4_le (b w0 w1 w2 w3 : BitVec 64) : b.toNat * v4 w0 w1 w2 w3 ≤ (2 ^ 64 - 1) * (2 ^ 256 - 1) := by
  have := b.isLt; have := v4_lt w0 w1 w2 w3
  exact Nat.mul_le_mul (by omega) (by omega)

/-- What a block of the `q·n` chain leaves: four words, and the carries, `cA` the `a·b` chain's word and
`cN` and `cf` the `q·n` chain's, and `of`, the last `adox`'s carry, which is zero. -/
structure Blk where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  cA : BitVec 64
  cN : BitVec 64
  cf : Bool
  of : Bool

/-- A block's `q·n` chain, onto the `a·b` chain's words `x` and the carry word `r`, from the carries `o`
(`adox`'s) and `c` (`adcx`'s). -/
def nphase (x0 x1 x2 x3 r n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) : Blk :=
  let y0 := adc x0 r o
  let z0 := adc y0.1 (mulLo q n0) c
  let y1 := adc x1 (mulHi q n0) y0.2
  let z1 := adc y1.1 (mulLo q n1) z0.2
  let y2 := adc x2 (mulHi q n1) y1.2
  let z2 := adc y2.1 (mulLo q n2) z1.2
  let y3 := adc x3 (mulHi q n2) y2.2
  let z3 := adc y3.1 (mulLo q n3) z2.2
  let y4 := adc0 (mulHi q n3) y3.2
  ⟨z0.1, z1.1, z2.1, z3.1, cA, y4.1, z3.2, y4.2⟩

theorem nphase_nat (x0 x1 x2 x3 r n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    let B := nphase x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA
    v4 B.w0 B.w1 B.w2 B.w3 + 2 ^ 256 * (B.cN.toNat + B.cf.toNat) =
      v4 x0 x1 x2 x3 + q.toNat * v4 n0 n1 n2 n3 + r.toNat + o.toNat + c.toNat := by
  simp only [nphase]
  have y0 := adc_nat x0 r o
  have z0 := adc_nat (adc x0 r o).1 (mulLo q n0) c
  have y1 := adc_nat x1 (mulHi q n0) (adc x0 r o).2
  have z1 := adc_nat (adc x1 (mulHi q n0) (adc x0 r o).2).1 (mulLo q n1) (adc (adc x0 r o).1 (mulLo q n0) c).2
  generalize adc x0 r o = Y0 at *
  generalize adc Y0.1 (mulLo q n0) c = Z0 at *
  generalize adc x1 (mulHi q n0) Y0.2 = Y1 at *
  generalize adc Y1.1 (mulLo q n1) Z0.2 = Z1 at *
  have y2 := adc_nat x2 (mulHi q n1) Y1.2
  generalize adc x2 (mulHi q n1) Y1.2 = Y2 at *
  have z2 := adc_nat Y2.1 (mulLo q n2) Z1.2
  generalize adc Y2.1 (mulLo q n2) Z1.2 = Z2 at *
  have y3 := adc_nat x3 (mulHi q n2) Y2.2
  generalize adc x3 (mulHi q n2) Y2.2 = Y3 at *
  have z3 := adc_nat Y3.1 (mulLo q n3) Z2.2
  generalize adc Y3.1 (mulLo q n3) Z2.2 = Z3 at *
  have y4 := adc0_nat (mulHi q n3) Y3.2
  have h3 := mulHi_le q n3
  have := (adc0 (mulHi q n3) Y3.2).1.isLt
  have hb : (adc0 (mulHi q n3) Y3.2).2.toNat = 0 := by
    have := Bool.toNat_le Y3.2; omega
  generalize adc0 (mulHi q n3) Y3.2 = Y4 at *
  have m0 := mul_toNat q n0; have m1 := mul_toNat q n1; have m2 := mul_toNat q n2; have m3 := mul_toNat q n3
  simp only [v4] at *
  rw [hb] at y4
  zify at *
  linear_combination z0 + y0 + (2 : ℤ) ^ 64 * (z1 + y1) + (2 : ℤ) ^ 128 * (z2 + y2) + (2 : ℤ) ^ 192 * (z3 + y3) +
    (2 : ℤ) ^ 256 * y4 + m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2 + (2 : ℤ) ^ 192 * m3

theorem nphase_cA (x0 x1 x2 x3 r n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    (nphase x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA).cA = cA := rfl

/-- `nphase_nat`'s carry out fits a word when the carries in do. -/
theorem nphase_lt (x0 x1 x2 x3 r n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64)
    (h : r.toNat + o.toNat + c.toNat < 2 ^ 64) :
    (nphase x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA).cN.toNat + (nphase x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA).cf.toNat
      < 2 ^ 64 := by
  have e := nphase_nat x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA
  have := mul_v4_le q n0 n1 n2 n3; have := v4_lt x0 x1 x2 x3
  generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
  generalize nphase x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA = B at *
  have := v4_lt B.w0 B.w1 B.w2 B.w3
  simp only at e
  omega

/-- Four words of the first pass, `first`: `a·b + q·n` onto the carries `cA`, `cN`, and `cf`. -/
def firstF (a0 a1 a2 a3 n0 n1 n2 n3 b q cA cN : BitVec 64) (cf : Bool) : Blk :=
  let r := adc0 cN cf
  let x0 := adc (mulLo b a0) cA r.2
  let x1 := adc (mulLo b a1) (mulHi b a0) x0.2
  let x2 := adc (mulLo b a2) (mulHi b a1) x1.2
  let x3 := adc (mulLo b a3) (mulHi b a2) x2.2
  let x4 := adc0 (mulHi b a3) x3.2
  nphase x0.1 x1.1 x2.1 x3.1 r.1 n0 n1 n2 n3 q false x4.2 x4.1

theorem toNat_eq_zero {c : Bool} (h : c.toNat = 0) : c = false := by cases c <;> simp_all

/-- The carries in a word, `cN + cf`, leave `adcx`'s first add without a carry. -/
theorem adc0_snd (x : BitVec 64) (c : Bool) (h : x.toNat + c.toNat < 2 ^ 64) : (adc0 x c).2 = false := by
  have h1 := adc0_nat x c; have h2 := (adc0 x c).1.isLt
  apply toNat_eq_zero; omega

theorem first_nat (a0 a1 a2 a3 n0 n1 n2 n3 b q cA cN : BitVec 64) (cf : Bool) (h : cN.toNat + cf.toNat < 2 ^ 64) :
    let F := firstF a0 a1 a2 a3 n0 n1 n2 n3 b q cA cN cf
    v4 F.w0 F.w1 F.w2 F.w3 + 2 ^ 256 * (F.cA.toNat + F.cN.toNat + F.cf.toNat) =
      b.toNat * v4 a0 a1 a2 a3 + q.toNat * v4 n0 n1 n2 n3 + cA.toNat + cN.toNat + cf.toNat ∧
    F.cN.toNat + F.cf.toNat < 2 ^ 64 := by
  simp only [firstF]
  have hr := adc0_nat cN cf
  have hr2 := adc0_snd cN cf h
  generalize adc0 cN cf = R at *
  have x0 := adc_nat (mulLo b a0) cA R.2
  generalize adc (mulLo b a0) cA R.2 = X0 at *
  have x1 := adc_nat (mulLo b a1) (mulHi b a0) X0.2
  generalize adc (mulLo b a1) (mulHi b a0) X0.2 = X1 at *
  have x2 := adc_nat (mulLo b a2) (mulHi b a1) X1.2
  generalize adc (mulLo b a2) (mulHi b a1) X1.2 = X2 at *
  have x3 := adc_nat (mulLo b a3) (mulHi b a2) X2.2
  generalize adc (mulLo b a3) (mulHi b a2) X2.2 = X3 at *
  have x4 := adc0_nat (mulHi b a3) X3.2
  generalize adc0 (mulHi b a3) X3.2 = X4 at *
  have m0 := mul_toNat b a0; have m1 := mul_toNat b a1; have m2 := mul_toNat b a2; have m3 := mul_toNat b a3
  have mA : v4 X0.1 X1.1 X2.1 X3.1 + 2 ^ 256 * X4.1.toNat + 2 ^ 320 * X4.2.toNat =
      b.toNat * v4 a0 a1 a2 a3 + cA.toNat + R.2.toNat := by
    simp only [v4] at *
    zify at *
    linear_combination x0 + (2 : ℤ) ^ 64 * x1 + (2 : ℤ) ^ 128 * x2 + (2 : ℤ) ^ 192 * x3 + (2 : ℤ) ^ 256 * x4 +
      m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2 + (2 : ℤ) ^ 192 * m3
  have hP := mul_v4_le b a0 a1 a2 a3
  have hcA := cA.isLt
  rw [hr2] at mA hr
  have h4 : X4.2 = false := by
    apply toNat_eq_zero
    clear * - mA hP hcA
    generalize b.toNat * v4 a0 a1 a2 a3 = P at *
    simp only [Bool.toNat_false] at mA
    omega
  rw [h4]
  have N := nphase_nat X0.1 X1.1 X2.1 X3.1 R.1 n0 n1 n2 n3 q false false X4.1
  have L := nphase_lt X0.1 X1.1 X2.1 X3.1 R.1 n0 n1 n2 n3 q false false X4.1 (by clear * - hr; simp at hr ⊢; omega)
  rw [nphase_cA]
  generalize nphase X0.1 X1.1 X2.1 X3.1 R.1 n0 n1 n2 n3 q false false X4.1 = B at *
  rw [h4] at mA
  simp only [Bool.toNat_false] at *
  refine ⟨?_, L⟩
  clear * - mA N hr
  generalize b.toNat * v4 a0 a1 a2 a3 = P at *
  generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
  omega

/-- Four words of an outer pass, `inner`: `a·b + q·n + t` onto the carries. -/
def innerF (a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q cA cN : BitVec 64) (cf : Bool) : Blk :=
  let r := adc0 cN cf
  let u0 := adc (mulLo b a0) cA false
  let v0 := adc u0.1 t0 r.2
  let u1 := adc (mulLo b a1) (mulHi b a0) u0.2
  let v1 := adc u1.1 t1 v0.2
  let u2 := adc (mulLo b a2) (mulHi b a1) u1.2
  let v2 := adc u2.1 t2 v1.2
  let u3 := adc (mulLo b a3) (mulHi b a2) u2.2
  let v3 := adc u3.1 t3 v2.2
  let u4 := adc0 (mulHi b a3) u3.2
  let w := adc0 u4.1 v3.2
  nphase v0.1 v1.1 v2.1 v3.1 r.1 n0 n1 n2 n3 q u4.2 w.2 w.1

theorem inner_nat (a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q cA cN : BitVec 64) (cf : Bool)
    (h : cN.toNat + cf.toNat < 2 ^ 64) :
    let F := innerF a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q cA cN cf
    v4 F.w0 F.w1 F.w2 F.w3 + 2 ^ 256 * (F.cA.toNat + F.cN.toNat + F.cf.toNat) =
      b.toNat * v4 a0 a1 a2 a3 + q.toNat * v4 n0 n1 n2 n3 + v4 t0 t1 t2 t3 + cA.toNat + cN.toNat + cf.toNat ∧
    F.cN.toNat + F.cf.toNat < 2 ^ 64 := by
  simp only [innerF]
  have hr := adc0_nat cN cf
  have hr2 := adc0_snd cN cf h
  generalize adc0 cN cf = R at *
  have u0 := adc_nat (mulLo b a0) cA false
  generalize adc (mulLo b a0) cA false = U0 at *
  have v0 := adc_nat U0.1 t0 R.2
  generalize adc U0.1 t0 R.2 = V0 at *
  have u1 := adc_nat (mulLo b a1) (mulHi b a0) U0.2
  generalize adc (mulLo b a1) (mulHi b a0) U0.2 = U1 at *
  have v1 := adc_nat U1.1 t1 V0.2
  generalize adc U1.1 t1 V0.2 = V1 at *
  have u2 := adc_nat (mulLo b a2) (mulHi b a1) U1.2
  generalize adc (mulLo b a2) (mulHi b a1) U1.2 = U2 at *
  have v2 := adc_nat U2.1 t2 V1.2
  generalize adc U2.1 t2 V1.2 = V2 at *
  have u3 := adc_nat (mulLo b a3) (mulHi b a2) U2.2
  generalize adc (mulLo b a3) (mulHi b a2) U2.2 = U3 at *
  have v3 := adc_nat U3.1 t3 V2.2
  generalize adc U3.1 t3 V2.2 = V3 at *
  have u4 := adc0_nat (mulHi b a3) U3.2
  generalize adc0 (mulHi b a3) U3.2 = U4 at *
  have w4 := adc0_nat U4.1 V3.2
  generalize adc0 U4.1 V3.2 = W4 at *
  have m0 := mul_toNat b a0; have m1 := mul_toNat b a1; have m2 := mul_toNat b a2; have m3 := mul_toNat b a3
  have mA : v4 V0.1 V1.1 V2.1 V3.1 + 2 ^ 256 * W4.1.toNat + 2 ^ 320 * (U4.2.toNat + W4.2.toNat) =
      b.toNat * v4 a0 a1 a2 a3 + v4 t0 t1 t2 t3 + cA.toNat + R.2.toNat := by
    simp only [v4, Bool.toNat_false] at *
    zify at *
    linear_combination u0 + v0 + (2 : ℤ) ^ 64 * (u1 + v1) + (2 : ℤ) ^ 128 * (u2 + v2) + (2 : ℤ) ^ 192 * (u3 + v3) +
      (2 : ℤ) ^ 256 * (u4 + w4) + m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2 + (2 : ℤ) ^ 192 * m3
  have hP := mul_v4_le b a0 a1 a2 a3
  have hcA := cA.isLt; have hT := v4_lt t0 t1 t2 t3
  rw [hr2] at mA hr
  have h4 : U4.2 = false ∧ W4.2 = false := by
    clear * - mA hP hcA hT
    generalize b.toNat * v4 a0 a1 a2 a3 = P at *
    simp only [Bool.toNat_false] at mA
    exact ⟨toNat_eq_zero (by omega), toNat_eq_zero (by omega)⟩
  rw [h4.1, h4.2]
  have N := nphase_nat V0.1 V1.1 V2.1 V3.1 R.1 n0 n1 n2 n3 q false false W4.1
  have L := nphase_lt V0.1 V1.1 V2.1 V3.1 R.1 n0 n1 n2 n3 q false false W4.1 (by clear * - hr; simp at hr ⊢; omega)
  rw [nphase_cA]
  generalize nphase V0.1 V1.1 V2.1 V3.1 R.1 n0 n1 n2 n3 q false false W4.1 = B at *
  rw [h4.1, h4.2] at mA
  simp only [Bool.toNat_false] at *
  refine ⟨?_, L⟩
  clear * - mA N hr
  generalize b.toNat * v4 a0 a1 a2 a3 = P at *
  generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
  omega

/-- A pass's first block's `q·n` chain, onto the `a·b` chain's words `x`, from the carries `o` and `c`: its
first word, which `q` zeroes, then three more. -/
def nhead (x0 x1 x2 x3 n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) : Blk :=
  let h0 := adc x0 (mulLo q n0) c
  let g1 := adc (mulHi q n0) x1 o
  let h1 := adc g1.1 (mulLo q n1) h0.2
  let g2 := adc (mulHi q n1) x2 g1.2
  let h2 := adc g2.1 (mulLo q n2) h1.2
  let g3 := adc (mulHi q n2) x3 g2.2
  let h3 := adc g3.1 (mulLo q n3) h2.2
  let g4 := adc0 (mulHi q n3) g3.2
  ⟨h0.1, h1.1, h2.1, h3.1, cA, g4.1, h3.2, g4.2⟩

theorem nhead_cA (x0 x1 x2 x3 n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    (nhead x0 x1 x2 x3 n0 n1 n2 n3 q o c cA).cA = cA := rfl

theorem nhead_w0 (x0 x1 x2 x3 n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    (nhead x0 x1 x2 x3 n0 n1 n2 n3 q o c cA).w0 = x0 + mulLo q n0 + (BitVec.ofBool c).setWidth 64 := rfl

theorem nhead_nat (x0 x1 x2 x3 n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    let B := nhead x0 x1 x2 x3 n0 n1 n2 n3 q o c cA
    v4 B.w0 B.w1 B.w2 B.w3 + 2 ^ 256 * (B.cN.toNat + B.cf.toNat) =
      v4 x0 x1 x2 x3 + q.toNat * v4 n0 n1 n2 n3 + c.toNat + 2 ^ 64 * o.toNat ∧
    B.cN.toNat + B.cf.toNat < 2 ^ 64 + 1 := by
  simp only [nhead]
  have h0 := adc_nat x0 (mulLo q n0) c
  generalize adc x0 (mulLo q n0) c = H0 at *
  have g1 := adc_nat (mulHi q n0) x1 o
  generalize adc (mulHi q n0) x1 o = G1 at *
  have h1 := adc_nat G1.1 (mulLo q n1) H0.2
  generalize adc G1.1 (mulLo q n1) H0.2 = H1 at *
  have g2 := adc_nat (mulHi q n1) x2 G1.2
  generalize adc (mulHi q n1) x2 G1.2 = G2 at *
  have h2 := adc_nat G2.1 (mulLo q n2) H1.2
  generalize adc G2.1 (mulLo q n2) H1.2 = H2 at *
  have g3 := adc_nat (mulHi q n2) x3 G2.2
  generalize adc (mulHi q n2) x3 G2.2 = G3 at *
  have h3 := adc_nat G3.1 (mulLo q n3) H2.2
  generalize adc G3.1 (mulLo q n3) H2.2 = H3 at *
  have g4 := adc0_nat (mulHi q n3) G3.2
  have hh := mulHi_le q n3
  have := (adc0 (mulHi q n3) G3.2).1.isLt
  have hb : (adc0 (mulHi q n3) G3.2).2.toNat = 0 := by have := Bool.toNat_le G3.2; omega
  generalize adc0 (mulHi q n3) G3.2 = G4 at *
  have m0 := mul_toNat q n0; have m1 := mul_toNat q n1; have m2 := mul_toNat q n2; have m3 := mul_toNat q n3
  rw [hb] at g4
  have e : v4 H0.1 H1.1 H2.1 H3.1 + 2 ^ 256 * (G4.1.toNat + H3.2.toNat) =
      v4 x0 x1 x2 x3 + q.toNat * v4 n0 n1 n2 n3 + c.toNat + 2 ^ 64 * o.toNat := by
    simp only [v4] at *
    zify at *
    linear_combination h0 + (2 : ℤ) ^ 64 * (g1 + h1) + (2 : ℤ) ^ 128 * (g2 + h2) + (2 : ℤ) ^ 192 * (g3 + h3) +
      (2 : ℤ) ^ 256 * g4 + m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2 + (2 : ℤ) ^ 192 * m3
  refine ⟨e, ?_⟩
  have := Bool.toNat_le H3.2
  omega

/-- `q = x·n0'` zeroes `x + q·n[0]`, for `n0' = -n[0]⁻¹ mod 2^64`. -/
theorem zero_word (x n0 n0' : BitVec 64) (h : (n0.toNat * n0'.toNat + 1) % 2 ^ 64 = 0) :
    x + mulLo (x * n0') n0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [mulLo, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_mul]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_mod, Nat.mod_mod, Nat.mod_mul_mod, ← Nat.add_mod,
    show x.toNat + x.toNat * n0'.toNat * n0.toNat = x.toNat * (n0.toNat * n0'.toNat + 1) by ring,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `body0`, the first pass's first four words, for `b = b[0]`: `a·b + q·n`, its low word zero. -/
def body0F (a0 a1 a2 a3 n0 n1 n2 n3 b q : BitVec 64) : Blk :=
  let s1 := (mulLo b a1 + mulHi b a0, decide (2 ^ 64 ≤ (mulLo b a1).toNat + (mulHi b a0).toNat))
  let s2 := adc (mulLo b a2) (mulHi b a1) s1.2
  let s3 := adc0 (mulHi b a2) s2.2
  let s4 := adc s3.1 (mulLo b a3) false
  let s5 := adc0 (mulHi b a3) s4.2
  nhead (mulLo b a0) s1.1 s2.1 s4.1 n0 n1 n2 n3 q false s5.2 s5.1

theorem body0_nat (a0 a1 a2 a3 n0 n1 n2 n3 b n0' : BitVec 64) (hn0 : (n0.toNat * n0'.toNat + 1) % 2 ^ 64 = 0) :
    let q := mulLo b a0 * n0'
    let F := body0F a0 a1 a2 a3 n0 n1 n2 n3 b q
    F.w0 = 0 ∧
    v4 F.w0 F.w1 F.w2 F.w3 + 2 ^ 256 * (F.cA.toNat + F.cN.toNat + F.cf.toNat) =
      b.toNat * v4 a0 a1 a2 a3 + q.toNat * v4 n0 n1 n2 n3 ∧
    F.cN.toNat + F.cf.toNat < 2 ^ 64 := by
  intro q
  simp only [body0F]
  have s1 : (mulLo b a1 + mulHi b a0).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (mulLo b a1).toNat + (mulHi b a0).toNat)).toNat =
      (mulLo b a1).toNat + (mulHi b a0).toNat := by
    have := adc_nat (mulLo b a1) (mulHi b a0) false
    simpa [adc] using this
  generalize mulLo b a1 + mulHi b a0 = S1 at *
  generalize decide (2 ^ 64 ≤ (mulLo b a1).toNat + (mulHi b a0).toNat) = c1 at *
  have s2 := adc_nat (mulLo b a2) (mulHi b a1) c1
  generalize adc (mulLo b a2) (mulHi b a1) c1 = S2 at *
  have s3 := adc0_nat (mulHi b a2) S2.2
  have hh := mulHi_le b a2
  have := (adc0 (mulHi b a2) S2.2).1.isLt
  have hb3 : (adc0 (mulHi b a2) S2.2).2.toNat = 0 := by have := Bool.toNat_le S2.2; omega
  generalize adc0 (mulHi b a2) S2.2 = S3 at *
  have s4 := adc_nat S3.1 (mulLo b a3) false
  generalize adc S3.1 (mulLo b a3) false = S4 at *
  have s5 := adc0_nat (mulHi b a3) S4.2
  generalize adc0 (mulHi b a3) S4.2 = S5 at *
  have m0 := mul_toNat b a0; have m1 := mul_toNat b a1; have m2 := mul_toNat b a2; have m3 := mul_toNat b a3
  rw [hb3] at s3
  have mA : v4 (mulLo b a0) S1 S2.1 S4.1 + 2 ^ 256 * S5.1.toNat + 2 ^ 320 * S5.2.toNat =
      b.toNat * v4 a0 a1 a2 a3 := by
    simp only [v4, Bool.toNat_false] at *
    zify at *
    linear_combination (2 : ℤ) ^ 64 * s1 + (2 : ℤ) ^ 128 * s2 + (2 : ℤ) ^ 192 * (s3 + s4) + (2 : ℤ) ^ 256 * s5 +
      m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2 + (2 : ℤ) ^ 192 * m3
  have hP := mul_v4_le b a0 a1 a2 a3
  have h5 : S5.2 = false := by
    apply toNat_eq_zero
    clear * - mA hP
    generalize b.toNat * v4 a0 a1 a2 a3 = P at *
    omega
  rw [h5]
  have N := nhead_nat (mulLo b a0) S1 S2.1 S4.1 n0 n1 n2 n3 q false false S5.1
  have hz := nhead_w0 (mulLo b a0) S1 S2.1 S4.1 n0 n1 n2 n3 q false false S5.1
  rw [nhead_cA]
  generalize nhead (mulLo b a0) S1 S2.1 S4.1 n0 n1 n2 n3 q false false S5.1 = B at *
  rw [h5] at mA
  simp only [Bool.toNat_false] at *
  have hw : B.w0 = 0 := by
    rw [hz]; simpa using zero_word (mulLo b a0) n0 n0' hn0
  refine ⟨hw, ?_, ?_⟩
  · clear * - mA N
    generalize b.toNat * v4 a0 a1 a2 a3 = P at *
    generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
    omega
  · have h1 := mul_v4_le q n0 n1 n2 n3
    have h2 := v4_lt (mulLo b a0) S1 S2.1 S4.1
    have h3 := v4_lt B.w0 B.w1 B.w2 B.w3
    clear * - N h1 h2 h3
    generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
    omega

/-- An outer pass's first four words, for `b = b[i]`: `a·b + q·n + t`, its low word zero. -/
def outerHeadF (a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q : BitVec 64) : Blk :=
  let p0 := adc (mulLo b a0) t0 false
  let c1 := adc (mulHi b a0) (mulLo b a1) false
  let p1 := adc c1.1 t1 p0.2
  let c2 := adc (mulHi b a1) (mulLo b a2) c1.2
  let p2 := adc c2.1 t2 p1.2
  let c3 := adc0 (mulHi b a2) c2.2
  let p3 := adc0 c3.1 p2.2
  let c4 := adc p3.1 (mulLo b a3) false
  let p4 := adc c4.1 t3 false
  let c5 := adc0 (mulHi b a3) c4.2
  let p5 := adc0 c5.1 p4.2
  nhead p0.1 p1.1 p2.1 p4.1 n0 n1 n2 n3 q p5.2 c5.2 p5.1

/-- The low word `outerHead`'s `q` is chosen by. -/
def outerHeadX (a0 t0 b : BitVec 64) : BitVec 64 := (adc (mulLo b a0) t0 false).1

theorem outerHead_nat (a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b n0' : BitVec 64)
    (hn0 : (n0.toNat * n0'.toNat + 1) % 2 ^ 64 = 0) :
    let q := outerHeadX a0 t0 b * n0'
    let F := outerHeadF a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q
    F.w0 = 0 ∧
    v4 F.w0 F.w1 F.w2 F.w3 + 2 ^ 256 * (F.cA.toNat + F.cN.toNat + F.cf.toNat) =
      b.toNat * v4 a0 a1 a2 a3 + q.toNat * v4 n0 n1 n2 n3 + v4 t0 t1 t2 t3 ∧
    F.cN.toNat + F.cf.toNat < 2 ^ 64 := by
  intro q
  simp only [outerHeadF]
  have p0 := adc_nat (mulLo b a0) t0 false
  generalize hP0 : adc (mulLo b a0) t0 false = P0 at *
  have c1 := adc_nat (mulHi b a0) (mulLo b a1) false
  generalize adc (mulHi b a0) (mulLo b a1) false = C1 at *
  have p1 := adc_nat C1.1 t1 P0.2
  generalize adc C1.1 t1 P0.2 = P1 at *
  have c2 := adc_nat (mulHi b a1) (mulLo b a2) C1.2
  generalize adc (mulHi b a1) (mulLo b a2) C1.2 = C2 at *
  have p2 := adc_nat C2.1 t2 P1.2
  generalize adc C2.1 t2 P1.2 = P2 at *
  have c3 := adc0_nat (mulHi b a2) C2.2
  generalize adc0 (mulHi b a2) C2.2 = C3 at *
  have p3 := adc0_nat C3.1 P2.2
  generalize adc0 C3.1 P2.2 = P3 at *
  have c4 := adc_nat P3.1 (mulLo b a3) false
  generalize adc P3.1 (mulLo b a3) false = C4 at *
  have p4 := adc_nat C4.1 t3 false
  generalize adc C4.1 t3 false = P4 at *
  have c5 := adc0_nat (mulHi b a3) C4.2
  generalize adc0 (mulHi b a3) C4.2 = C5 at *
  have p5 := adc0_nat C5.1 P4.2
  generalize adc0 C5.1 P4.2 = P5 at *
  have m0 := mul_toNat b a0; have m1 := mul_toNat b a1; have m2 := mul_toNat b a2; have m3 := mul_toNat b a3
  -- The low three words: below `2^256`, so the carries `c3` and `p3` drop are zero.
  have m3w : P0.1.toNat + 2 ^ 64 * P1.1.toNat + 2 ^ 128 * P2.1.toNat + 2 ^ 192 * P3.1.toNat +
      2 ^ 256 * (C3.2.toNat + P3.2.toNat) =
      b.toNat * (a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat) + (t0.toNat + 2 ^ 64 * t1.toNat + 2 ^ 128 * t2.toNat) := by
    simp only [Bool.toNat_false] at *
    zify at *
    linear_combination p0 + (2 : ℤ) ^ 64 * (c1 + p1) + (2 : ℤ) ^ 128 * (c2 + p2) + (2 : ℤ) ^ 192 * (c3 + p3) +
      m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2
  have h3 : C3.2 = false ∧ P3.2 = false := by
    have hb : b.toNat * (a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat) ≤ (2 ^ 64 - 1) * (2 ^ 192 - 1) := by
      have := b.isLt; have := a0.isLt; have := a1.isLt; have := a2.isLt
      exact Nat.mul_le_mul (by omega) (by omega)
    have h0 := t0.isLt; have h1 := t1.isLt; have h2 := t2.isLt
    clear * - m3w hb h0 h1 h2
    generalize b.toNat * (a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat) = P at *
    exact ⟨toNat_eq_zero (by omega), toNat_eq_zero (by omega)⟩
  rw [h3.1] at c3; rw [h3.2] at p3
  have mA : v4 P0.1 P1.1 P2.1 P4.1 + 2 ^ 256 * P5.1.toNat + 2 ^ 320 * (C5.2.toNat + P5.2.toNat) =
      b.toNat * v4 a0 a1 a2 a3 + v4 t0 t1 t2 t3 := by
    simp only [v4, Bool.toNat_false] at *
    zify at *
    linear_combination p0 + (2 : ℤ) ^ 64 * (c1 + p1) + (2 : ℤ) ^ 128 * (c2 + p2) + (2 : ℤ) ^ 192 * (c3 + p3 + c4 + p4) +
      (2 : ℤ) ^ 256 * (c5 + p5) + m0 + (2 : ℤ) ^ 64 * m1 + (2 : ℤ) ^ 128 * m2 + (2 : ℤ) ^ 192 * m3
  have hP := mul_v4_le b a0 a1 a2 a3
  have hT := v4_lt t0 t1 t2 t3
  have h5 : C5.2 = false ∧ P5.2 = false := by
    clear * - mA hP hT
    generalize b.toNat * v4 a0 a1 a2 a3 = P at *
    exact ⟨toNat_eq_zero (by omega), toNat_eq_zero (by omega)⟩
  rw [h5.1, h5.2]
  have N := nhead_nat P0.1 P1.1 P2.1 P4.1 n0 n1 n2 n3 q false false P5.1
  have hz := nhead_w0 P0.1 P1.1 P2.1 P4.1 n0 n1 n2 n3 q false false P5.1
  rw [nhead_cA]
  have hq : q = P0.1 * n0' := by simp only [q, outerHeadX, hP0]
  generalize nhead P0.1 P1.1 P2.1 P4.1 n0 n1 n2 n3 q false false P5.1 = B at *
  rw [h5.1, h5.2] at mA
  simp only [Bool.toNat_false] at *
  have hw : B.w0 = 0 := by
    rw [hz, hq]; simpa using zero_word P0.1 n0 n0' hn0
  refine ⟨hw, ?_, ?_⟩
  · clear * - mA N
    generalize b.toNat * v4 a0 a1 a2 a3 = P at *
    generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
    omega
  · have h1 := mul_v4_le q n0 n1 n2 n3
    have h2 := v4_lt P0.1 P1.1 P2.1 P4.1
    have h3 := v4_lt B.w0 B.w1 B.w2 B.w3
    clear * - N h1 h2 h3
    generalize q.toNat * v4 n0 n1 n2 n3 = Q at *
    omega

theorem adc0_mulHi (a b : BitVec 64) (c : Bool) : (adc0 (mulHi a b) c).2 = false := by
  have h1 := adc0_nat (mulHi a b) c; have h2 := mulHi_le a b; have h3 := Bool.toNat_le c
  have := (adc0 (mulHi a b) c).1.isLt
  apply toNat_eq_zero; omega

theorem nphase_of (x0 x1 x2 x3 r n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    (nphase x0 x1 x2 x3 r n0 n1 n2 n3 q o c cA).of = false := adc0_mulHi _ _ _

theorem nhead_of (x0 x1 x2 x3 n0 n1 n2 n3 q : BitVec 64) (o c : Bool) (cA : BitVec 64) :
    (nhead x0 x1 x2 x3 n0 n1 n2 n3 q o c cA).of = false := adc0_mulHi _ _ _

/-- A pass's top word: the last block's carries `cA`, `cN`, and `cf`, `adc` and `add` into `cA`, and the carry
out. -/
def topF (cA cN : BitVec 64) (cf : Bool) : BitVec 64 × Bool :=
  let r := adc0 cN cf
  (cA + r.1, decide (2 ^ 64 ≤ cA.toNat + r.1.toNat))

theorem add2_nat (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat = x.toNat + y.toNat := by
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

theorem topF_nat (cA cN : BitVec 64) (cf : Bool) (h : cN.toNat + cf.toNat < 2 ^ 64) :
    (topF cA cN cf).1.toNat + 2 ^ 64 * (topF cA cN cf).2.toNat = cA.toNat + cN.toNat + cf.toNat := by
  have hr := adc0_nat cN cf
  have hr2 := adc0_snd cN cf h
  simp only [topF]
  rw [add2_nat]
  rw [hr2] at hr
  simp only [Bool.toNat_false] at hr
  omega

/-- An outer pass's top word: `topF` with the last pass's top bit `c`, read from the word `0 - c` by
subtracting it from 0, added in. -/
def topT (cA cN T : BitVec 64) (cf : Bool) : BitVec 64 × Bool :=
  adc cA (adc0 cN cf).1 (decide ((0 : BitVec 64).toNat < T.toNat))

theorem negBit (c : Bool) : decide ((0 : BitVec 64).toNat < (0 - (BitVec.ofBool c).setWidth 64).toNat) = c := by
  cases c <;> decide

theorem topT_nat (cA cN : BitVec 64) (cf c : Bool) (h : cN.toNat + cf.toNat < 2 ^ 64) :
    (topT cA cN (0 - (BitVec.ofBool c).setWidth 64) cf).1.toNat +
        2 ^ 64 * (topT cA cN (0 - (BitVec.ofBool c).setWidth 64) cf).2.toNat =
      cA.toNat + cN.toNat + cf.toNat + c.toNat := by
  have hr := adc0_nat cN cf
  have hr2 := adc0_snd cN cf h
  simp only [topT, negBit]
  rw [adc_nat]
  rw [hr2] at hr
  simp only [Bool.toNat_false] at hr
  omega

end rind.x86_64.mulx4x
