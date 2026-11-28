import Rind.X86_64.Mulx4xAsm
import Rind.X86_64.Mul4xOuter
import Rind.X86_64.Mul4xFinal

/-! # bn_mulx4x_mont's passes

A pass's loop of four-word blocks, the first pass, an outer pass, and the loop of outer passes. A pass leaves
`t`'s `k` words in the frame from word 8 and its top bit `c` in `r15` as `0 - c`; after pass `i`,
`V = t + 2^(64k)·c` has `2^(64i)·V = a·b_i + Q·n` for some `Q`, `b_i` the low `i` words of `b`, and `V < a + n`. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

namespace rind.x86_64.mulx4x

theorem Arr.frame {s s' : S} {k : Nat} {ap bp np fp : Addr} {gs : List Reg} (ar : Arr s k ap bp np fp)
    (h : Frame s s' gs) : Arr s' k ap bp np fp := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, rF⟩ := ar
  rw [← h.rd, ← h.wr] at rA rB rN
  rw [← h.wr] at rF
  exact ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, rF⟩

/-- Word `i` of the frame's `t`. -/
abbrev tw (M : Mem) (fp : Addr) (i : Nat) : BitVec 64 := M.readW (wa fp (i + 8)) 64

/-! ## Memory within a pass -/

theorem _root_.rind.x86_64.mul4x.Agree.writeT {M₀ M : Mem} {fp : Addr} {j : Nat} (v : BitVec 64) (h : Agree M₀ M (wa fp 8) j) :
    Agree M₀ (M.writeW (wa fp (j + 8)) v) (wa fp 8) (j + 1) := by
  intro y hy
  have := (y - wa fp 8).isLt
  have e : (M.writeW (wa fp (j + 8)) v) y = M y := by
    unfold Mem.writeW; apply write_other; simp only [wa] at hy ⊢; bv_omega
  rw [e]; exact h y (by omega)

/-- A word of an array apart from the frame keeps its value. -/
theorem _root_.rind.x86_64.mul4x.Agree.arrF {M₀ M : Mem} {fp p : Addr} {j k i : Nat} (h : Agree M₀ M (wa fp 8) j) (hj : j ≤ k + 1)
    (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (hp : p.toNat + 8 * k ≤ 2 ^ 64)
    (sep : p.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ p.toNat) (hi : i < k) :
    M.readW (wa p i) 64 = M₀.readW (wa p i) 64 :=
  readW_agree h fun b hb => by simp only [wa]; bv_omega

/-- A slot of the frame keeps its value. -/
theorem _root_.rind.x86_64.mul4x.Agree.slotF {M₀ M : Mem} {fp : Addr} {j k i : Nat} (h : Agree M₀ M (wa fp 8) j) (hj : j ≤ k + 1)
    (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (hi : i < 8) :
    M.readW (wa fp i) 64 = M₀.readW (wa fp i) 64 :=
  readW_agree h fun b hb => by simp only [wa]; bv_omega

/-- A word of `t` at or past `j` keeps its value. -/
theorem _root_.rind.x86_64.mul4x.Agree.twF {M₀ M : Mem} {fp : Addr} {j k i : Nat} (h : Agree M₀ M (wa fp 8) j) (hji : j ≤ i) (hi : i ≤ k)
    (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) :
    M.readW (wa fp (i + 8)) 64 = M₀.readW (wa fp (i + 8)) 64 :=
  readW_agree h fun b hb => by simp only [wa]; bv_omega

/-! ## Memory across passes -/

/-- `M` matches `M₀` but in the frame's slot 1 and `t`'s `k + 1` words. -/
def Keep (M₀ M : Mem) (fp : Addr) (k : Nat) : Prop :=
  ∀ y, 8 ≤ (y - wa fp 1).toNat → 8 * (k + 1) ≤ (y - wa fp 8).toNat → M y = M₀ y

theorem Keep.refl (M : Mem) (fp : Addr) (k : Nat) : Keep M M fp k := fun _ _ _ => rfl

theorem Keep.trans {M₀ M₁ M₂ : Mem} {fp : Addr} {k : Nat} (h₁ : Keep M₀ M₁ fp k) (h₂ : Keep M₁ M₂ fp k) :
    Keep M₀ M₂ fp k :=
  fun y a b => (h₂ y a b).trans (h₁ y a b)

theorem Keep.agree {M₀ M₁ M₂ : Mem} {fp : Addr} {k j : Nat} (h : Keep M₀ M₁ fp k)
    (h' : Agree M₁ M₂ (wa fp 8) j) (hj : j ≤ k + 1) : Keep M₀ M₂ fp k :=
  fun y a b => (h' y (by omega)).trans (h y a b)

theorem Keep.writeT {M₀ M : Mem} {fp : Addr} {k i : Nat} (v : BitVec 64) (h : Keep M₀ M fp k) (hi : i ≤ k) :
    Keep M₀ (M.writeW (wa fp (i + 8)) v) fp k := by
  intro y h1 h2
  have e : (M.writeW (wa fp (i + 8)) v) y = M y := by
    unfold Mem.writeW; apply write_other; simp only [wa] at h2 ⊢; bv_omega
  rw [e]; exact h y h1 h2

theorem Keep.write1 {M₀ M : Mem} {fp : Addr} {k : Nat} (v : BitVec 64) (h : Keep M₀ M fp k) :
    Keep M₀ (M.writeW (wa fp 1) v) fp k := by
  intro y h1 h2
  have e : (M.writeW (wa fp 1) v) y = M y := by unfold Mem.writeW; exact write_other _ _ _ _ _ h1
  rw [e]; exact h y h1 h2

theorem Keep.readW {M₀ M : Mem} {fp x : Addr} {k : Nat} (h : Keep M₀ M fp k)
    (hx : ∀ c < 8, 8 ≤ (x + BitVec.ofNat 64 c - wa fp 1).toNat ∧
      8 * (k + 1) ≤ (x + BitVec.ofNat 64 c - wa fp 8).toNat) : M.readW x 64 = M₀.readW x 64 := by
  simp only [Mem.readW]; congr 1; apply read_congr; intro c hc
  exact h _ (hx c (by omega)).1 (hx c (by omega)).2

/-- A word of an array apart from the frame keeps its value. -/
theorem Keep.arr {M₀ M : Mem} {fp p : Addr} {k i : Nat} (h : Keep M₀ M fp k)
    (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (hp : p.toNat + 8 * k ≤ 2 ^ 64)
    (sep : p.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ p.toNat) (hi : i < k) :
    M.readW (wa p i) 64 = M₀.readW (wa p i) 64 :=
  h.readW fun c hc => by simp only [wa]; constructor <;> bv_omega

/-- A slot of the frame but slot 1 keeps its value. -/
theorem Keep.slot {M₀ M : Mem} {fp : Addr} {k i : Nat} (h : Keep M₀ M fp k)
    (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (hi : i < 8) (h1 : i ≠ 1) :
    M.readW (wa fp i) 64 = M₀.readW (wa fp i) 64 :=
  h.readW fun c hc => by simp only [wa]; constructor <;> bv_omega

/-- The frame's slots that `setup` stores and the passes keep. -/
structure Slots (M : Mem) (k : Nat) (bp fp rp sp0 n0' : Addr) : Prop where
  s0 : M.readW (wa fp 0) 64 = BitVec.ofNat 64 (8 * k)
  s2 : M.readW (wa fp 2) 64 = wa bp k
  s3 : M.readW (wa fp 3) 64 = n0'
  s4 : M.readW (wa fp 4) 64 = rp
  s5 : M.readW (wa fp 5) 64 = sp0
  s6 : M.readW (wa fp 6) 64 = BitVec.ofNat 64 (k / 4 - 1)

theorem Slots.keep {M₀ M : Mem} {k : Nat} {bp fp rp sp0 n0' : Addr} (sl : Slots M₀ k bp fp rp sp0 n0')
    (h : Keep M₀ M fp k) (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) : Slots M k bp fp rp sp0 n0' :=
  ⟨(h.slot hfp (by omega) (by omega)).trans sl.s0, (h.slot hfp (by omega) (by omega)).trans sl.s2,
    (h.slot hfp (by omega) (by omega)).trans sl.s3, (h.slot hfp (by omega) (by omega)).trans sl.s4,
    (h.slot hfp (by omega) (by omega)).trans sl.s5, (h.slot hfp (by omega) (by omega)).trans sl.s6⟩

/-! ## Arithmetic -/

theorem val_add4 (f : Nat → BitVec 64) (j : Nat) :
    val f (j + 4) = val f j + 2 ^ (64 * j) * v4 (f j) (f (j + 1)) (f (j + 2)) (f (j + 3)) := by
  show gsum _ (j + 1 + 1 + 1 + 1) = _
  simp only [gsum, v4]
  have e1 : 2 ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  have e2 : 2 ^ (64 * (j + 1 + 1)) = 2 ^ (64 * j) * 2 ^ 128 := by
    rw [show 64 * (j + 1 + 1) = 64 * j + 128 by ring, Nat.pow_add]
  have e3 : 2 ^ (64 * (j + 1 + 1 + 1)) = 2 ^ (64 * j) * 2 ^ 192 := by
    rw [show 64 * (j + 1 + 1 + 1) = 64 * j + 192 by ring, Nat.pow_add]
  rw [e1, e2, e3]; ring

theorem val_zero (m : Nat) : val (fun _ => (0 : BitVec 64)) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [val, gsum] at ih ⊢; rw [ih]; simp

theorem val_four (f : Nat → BitVec 64) : val f 4 = v4 (f 0) (f 1) (f 2) (f 3) := by
  have := val_add4 f 0; simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at this
  rw [this]; simp only [val, gsum, Nat.zero_add]

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

theorem val_three (f : Nat → BitVec 64) :
    2 ^ 64 * val f 3 = v4 0 (f 0) (f 1) (f 2) := by
  show 2 ^ 64 * gsum _ (0 + 1 + 1 + 1) = _
  simp only [gsum, v4, toNat_zero64]; ring

/-- Four more words of a pass keep its identity. -/
theorem chain_step (Wj Aj Nj Tj b q c V VA VN VT c' P Q : Nat) (hP : P = 2 ^ 64 * Q)
    (hI : 2 ^ 64 * Wj + P * c = b * Aj + q * Nj + Tj)
    (hF : V + 2 ^ 256 * c' = b * VA + q * VN + VT + c) :
    2 ^ 64 * (Wj + Q * V) + P * 2 ^ 256 * c' = b * (Aj + P * VA) + q * (Nj + P * VN) + (Tj + P * VT) := by
  subst hP; zify at *; linear_combination hI + (2 : ℤ) ^ 64 * Q * hF

theorem subOverflow_dec (c : Nat) (h1 : 1 ≤ c) (h : c < 2 ^ 63) :
    subOverflow (BitVec.ofNat 64 c) 1 (BitVec.ofNat 64 c - 1) = false := by
  rw [(dec_ne c h1 (by omega)).1]
  have m1 : (BitVec.ofNat 64 c).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have m2 : (BitVec.ofNat 64 (c - 1)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  simp only [subOverflow, m1, m2]; decide

theorem eval_ne {s : S} {z : Bool} (h : s.vg.zf = some z) : I.eval (Rind.X86_64.Cond.vg .ne) s = some (!z) := by
  simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, h, Option.map_some]

/-! ## A pass's loop -/

/-- A pass's loop before its block at word `j + 1`: the words of `t` below `j` stored, the carries, and what
they add up to; `T` is the last pass's `t`, zero in the first pass. -/
structure PInv (s₁ s : S) (k : Nat) (ap np fp : Addr) (a n T : Nat → BitVec 64) (b q : BitVec 64) (j : Nat) :
    Prop where
  j3 : j % 4 = 3
  jk : j + 1 ≤ k
  frame : Frame s₁ s [.rax, .rdx, .rdi, .rsi, .rcx, .rbx, .r10, .r11, .r12, .r13, .r14, .r15]
  rsi : s.vg.gpr .rsi = wa ap (j + 1)
  rcx : s.vg.gpr .rcx = wa np (j + 1)
  rbx : s.vg.gpr .rbx = wa fp (j + 9)
  rdx : s.vg.gpr .rdx = b
  rdi : s.vg.gpr .rdi = BitVec.ofNat 64 ((k - 1 - j) / 4)
  of : s.vg.of = some false
  agree : Agree s₁.vg.mem s.vg.mem (wa fp 8) j
  sum : ∃ cA cN : BitVec 64, ∃ cf : Bool, s.vg.gpr .r14 = cA ∧ s.vg.gpr .r15 = cN ∧ s.vg.cf = some cf ∧
    cN.toNat + cf.toNat < 2 ^ 64 ∧
    2 ^ 64 * val (tw s.vg.mem fp) j + 2 ^ (64 * (j + 1)) * (cA.toNat + cN.toNat + cf.toNat) =
      b.toNat * val a (j + 1) + q.toNat * val n (j + 1) + val T (j + 1)

/-- The words of `t` after a block's four stores. -/
theorem tw_four {M : Mem} {fp : Addr} {k j : Nat} (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (hj : j + 4 ≤ k)
    (w0 w1 w2 w3 : BitVec 64) :
    let M' := (((M.writeW (wa fp (j + 8)) w0).writeW (wa fp (j + 9)) w1).writeW (wa fp (j + 10)) w2).writeW
      (wa fp (j + 11)) w3
    val (tw M' fp) (j + 4) = val (tw M fp) j + 2 ^ (64 * j) * v4 w0 w1 w2 w3 := by
  intro M'
  rw [val_add4]
  have hw : ∀ i < j, tw M' fp i = tw M fp i := fun i hi => by
    simp only [tw, M']
    rw [readW_wa_ne _ hfp (by omega) (by omega) (by omega), readW_wa_ne _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne _ hfp (by omega) (by omega) (by omega), readW_wa_ne _ hfp (by omega) (by omega) (by omega)]
  rw [show val (tw M' fp) j = val (tw M fp) j from gsum_congr fun i hi => by rw [hw i hi]]
  congr 2
  simp only [tw, M']
  rw [readW_wa_ne _ hfp (by omega) (by omega) (by omega), readW_wa_ne _ hfp (by omega) (by omega) (by omega),
    readW_wa_ne _ hfp (by omega) (by omega) (by omega), readW_writeW_self, show j + 1 + 8 = j + 9 by omega,
    readW_wa_ne _ hfp (by omega) (by omega) (by omega), readW_wa_ne _ hfp (by omega) (by omega) (by omega),
    readW_writeW_self, show j + 2 + 8 = j + 10 by omega, readW_wa_ne _ hfp (by omega) (by omega) (by omega),
    readW_writeW_self, show j + 3 + 8 = j + 11 by omega, readW_writeW_self]

/-- The `Agree` four stores keep. -/
theorem agree_four (M : Mem) (fp : Addr) (j : Nat) (w0 w1 w2 w3 : BitVec 64) :
    Agree M ((((M.writeW (wa fp (j + 8)) w0).writeW (wa fp (j + 9)) w1).writeW (wa fp (j + 10)) w2).writeW
      (wa fp (j + 11)) w3) (wa fp 8) (j + 4) :=
  (((Agree.refl M _ j).writeT w0).writeT w1 |>.writeT w2).writeT w3

/-- What a block's identity and the loop's before it add up to. -/
theorem sum_step {M : Mem} {fp : Addr} {k j : Nat} (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (hj : j + 4 ≤ k)
    (a n T : Nat → BitVec 64) (b q cA cN : BitVec 64) (cf : Bool) (F : Blk)
    (hI : 2 ^ 64 * val (tw M fp) j + 2 ^ (64 * (j + 1)) * (cA.toNat + cN.toNat + cf.toNat) =
      b.toNat * val a (j + 1) + q.toNat * val n (j + 1) + val T (j + 1))
    (hF : v4 F.w0 F.w1 F.w2 F.w3 + 2 ^ 256 * (F.cA.toNat + F.cN.toNat + F.cf.toNat) =
      b.toNat * v4 (a (j + 1)) (a (j + 2)) (a (j + 3)) (a (j + 4)) +
        q.toNat * v4 (n (j + 1)) (n (j + 2)) (n (j + 3)) (n (j + 4)) +
        v4 (T (j + 1)) (T (j + 2)) (T (j + 3)) (T (j + 4)) + (cA.toNat + cN.toNat + cf.toNat)) :
    let M' := (((M.writeW (wa fp (j + 8)) F.w0).writeW (wa fp (j + 9)) F.w1).writeW (wa fp (j + 10)) F.w2).writeW
      (wa fp (j + 11)) F.w3
    2 ^ 64 * val (tw M' fp) (j + 4) + 2 ^ (64 * (j + 4 + 1)) * (F.cA.toNat + F.cN.toNat + F.cf.toNat) =
      b.toNat * val a (j + 4 + 1) + q.toNat * val n (j + 4 + 1) + val T (j + 4 + 1) := by
  intro M'
  rw [tw_four hfp hj, show j + 4 + 1 = j + 1 + 4 by omega, val_add4 a, val_add4 n, val_add4 T,
    show 64 * (j + 1 + 4) = 64 * (j + 1) + 256 by ring, Nat.pow_add]
  exact chain_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]) hI
    (by rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega, show j + 1 + 3 = j + 4 by omega]
        exact hF)

theorem first_step (s₁ : S) (k : Nat) (ap bp np fp b q : Addr) (a n : Nat → BitVec 64)
    (ar : Arr s₁ k ap bp np fp) (hr9 : s₁.vg.gpr .r9 = b) (hr8 : s₁.vg.gpr .r8 = q) (hrbp : s₁.vg.gpr .rbp = 0)
    (hA : ∀ i < k, s₁.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₁.vg.mem.readW (wa np i) 64 = n i)
    (hk4 : k % 4 = 0) (j : Nat) (s : S) (hI : PInv s₁ s k ap np fp a n (fun _ => 0) b q j) (hR : j + 5 ≤ k) :
    ∃ s', Exec I (.block Rind.X86_64.Mulx4x.first) s (firstTrace ap np fp j) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (j + 5 < k)) ∧
      PInv s₁ s' k ap np fp a n (fun _ => 0) b q (j + 4) := by
  have hF := hI.frame
  have hfp := ar.hfp
  have hk := ar.k29
  have j3 := hI.j3
  have g : ∀ r, r ∉ [Reg.rax, .rdx, .rdi, .rsi, .rcx, .rbx, .r10, .r11, .r12, .r13, .r14, .r15] →
      s.vg.gpr r = s₁.vg.gpr r := hF.gpr
  obtain ⟨d1, d2⟩ := dec_ne ((k - 1 - j) / 4) (by omega) (by omega)
  have e1 : (decide (1 < (k - 1 - j) / 4)) = decide (j + 5 < k) := by simp only [decide_eq_decide]; omega
  have e2 : (k - 1 - j) / 4 - 1 = (k - 1 - (j + 4)) / 4 := by omega
  have o1 := subOverflow_dec ((k - 1 - j) / 4) (by omega) (by omega)
  obtain ⟨cA, cN, cf, h14, h15, hcf, hlt, hsum⟩ := hI.sum
  obtain ⟨s', hx, osi, ocx, obx, odx, o14, o15, ocf, odi, ozf, oof, omem, oF⟩ :=
    first_ok s j k ((k - 1 - j) / 4) ap bp np fp b q cA cN cf a n hR (ar.frame hF) hI.rsi hI.rcx hI.rbx
      ((g .r9 (by decide)).trans hr9) hI.rdx ((g .r8 (by decide)).trans hr8) ((g .rbp (by decide)).trans hrbp)
      h14 h15 hI.rdi hcf hI.of
      (fun i hi => (hI.agree.arrF (by omega) hfp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (hI.agree.arrF (by omega) hfp ar.hnp ar.sepN hi).trans (hN i hi))
  have FN := first_nat (a (j + 1)) (a (j + 2)) (a (j + 3)) (a (j + 4)) (n (j + 1)) (n (j + 2)) (n (j + 3))
    (n (j + 4)) b q cA cN cf hlt
  refine ⟨s', Exec.block hx, ?_, ?_⟩
  · rw [eval_ne ozf, d2, e1]
  refine ⟨by omega, by omega, hF.trans oF, osi, ocx, obx, odx, ?_, ?_, ?_, ⟨_, _, _, o14, o15, ocf, FN.2, ?_⟩⟩
  · rw [odi, d1, e2]
  · rw [oof, o1]
  · rw [omem]; exact hI.agree.trans (agree_four _ _ _ _ _ _ _) (by omega)
  · rw [omem]
    refine sum_step hfp (by omega) a n (fun _ => 0) b q cA cN cf _ hsum ?_
    rw [FN.1]; simp only [toNat_zero64, v4]; ring

theorem inner_step (s₁ : S) (k : Nat) (ap bp np fp b q : Addr) (a n T : Nat → BitVec 64)
    (ar : Arr s₁ k ap bp np fp) (hr9 : s₁.vg.gpr .r9 = b) (hr8 : s₁.vg.gpr .r8 = q) (hrbp : s₁.vg.gpr .rbp = 0)
    (hA : ∀ i < k, s₁.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₁.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i, 3 ≤ i → i < k → s₁.vg.mem.readW (wa fp (i + 8)) 64 = T i)
    (hk4 : k % 4 = 0) (j : Nat) (s : S) (hI : PInv s₁ s k ap np fp a n T b q j) (hR : j + 5 ≤ k) :
    ∃ s', Exec I (.block Rind.X86_64.Mulx4x.inner) s (innerTrace ap np fp j) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (j + 5 < k)) ∧
      PInv s₁ s' k ap np fp a n T b q (j + 4) := by
  have hF := hI.frame
  have hfp := ar.hfp
  have hk := ar.k29
  have j3 := hI.j3
  have g : ∀ r, r ∉ [Reg.rax, .rdx, .rdi, .rsi, .rcx, .rbx, .r10, .r11, .r12, .r13, .r14, .r15] →
      s.vg.gpr r = s₁.vg.gpr r := hF.gpr
  obtain ⟨d1, d2⟩ := dec_ne ((k - 1 - j) / 4) (by omega) (by omega)
  have e1 : (decide (1 < (k - 1 - j) / 4)) = decide (j + 5 < k) := by simp only [decide_eq_decide]; omega
  have e2 : (k - 1 - j) / 4 - 1 = (k - 1 - (j + 4)) / 4 := by omega
  have o1 := subOverflow_dec ((k - 1 - j) / 4) (by omega) (by omega)
  obtain ⟨cA, cN, cf, h14, h15, hcf, hlt, hsum⟩ := hI.sum
  obtain ⟨s', hx, osi, ocx, obx, odx, o14, o15, ocf, odi, ozf, oof, omem, oF⟩ :=
    inner_ok s j k ((k - 1 - j) / 4) ap bp np fp b q cA cN cf a n (fun i => T (i - 8)) hR (ar.frame hF) hI.rsi
      hI.rcx hI.rbx ((g .r9 (by decide)).trans hr9) hI.rdx ((g .r8 (by decide)).trans hr8)
      ((g .rbp (by decide)).trans hrbp) h14 h15 hI.rdi hcf hI.of
      (fun i hi => (hI.agree.arrF (by omega) hfp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (hI.agree.arrF (by omega) hfp ar.hnp ar.sepN hi).trans (hN i hi))
      (fun i h1 h2 => by
        have := (hI.agree.twF (k := k) (i := i - 8) (by omega) (by omega) hfp).trans
          (hT (i - 8) (by omega) (by omega))
        rwa [show i - 8 + 8 = i by omega] at this)
  simp only [show j + 9 - 8 = j + 1 by omega, show j + 10 - 8 = j + 2 by omega, show j + 11 - 8 = j + 3 by omega,
    show j + 12 - 8 = j + 4 by omega] at o14 o15 ocf omem
  have FN := inner_nat (a (j + 1)) (a (j + 2)) (a (j + 3)) (a (j + 4)) (n (j + 1)) (n (j + 2)) (n (j + 3))
    (n (j + 4)) (T (j + 1)) (T (j + 2)) (T (j + 3)) (T (j + 4)) b q cA cN cf hlt
  refine ⟨s', Exec.block hx, ?_, ?_⟩
  · rw [eval_ne ozf, d2, e1]
  refine ⟨by omega, by omega, hF.trans oF, osi, ocx, obx, odx, ?_, ?_, ?_, ⟨_, _, _, o14, o15, ocf, FN.2, ?_⟩⟩
  · rw [odi, d1, e2]
  · rw [oof, o1]
  · rw [omem]; exact hI.agree.trans (agree_four _ _ _ _ _ _ _) (by omega)
  · rw [omem]
    refine sum_step hfp (by omega) a n T b q cA cN cf _ hsum ?_
    rw [FN.1]; ring

end rind.x86_64.mulx4x
