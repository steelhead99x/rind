import Rind.X86_64.Mulx4xPass
import Rind.X86_64.Mulx4xTail

/-! # bn_mulx4x_mont's subtraction and selection

`final`, the loop of `sub`, `subTail`, and the loop of `copy`: `t - n` into `rp`, then `t` or `t - n` by the
mask the top bit and the last borrow make, which is `V mod n` for `V < 2n`. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mulx4x

theorem Arr.frameX {s s' : S} {k : Nat} {ap bp np fp : Addr} {gs : List Reg} (ar : Arr s k ap bp np fp)
    (h : FrameX s s' gs) : Arr s' k ap bp np fp := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, rF⟩ := ar
  rw [← h.rd, ← h.wr] at rA rB rN
  rw [← h.wr] at rF
  exact ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, rF⟩

theorem OutX.frame {s s' : S} {k : Nat} {np fp rp : Addr} {gs : List Reg} (out : OutX s k np fp rp)
    (h : Frame s s' gs) : OutX s' k np fp rp :=
  ⟨out.hrp, out.sepF, out.sepN, h.wr ▸ out.rP⟩

theorem OutX.frameX {s s' : S} {k : Nat} {np fp rp : Addr} {gs : List Reg} (out : OutX s k np fp rp)
    (h : FrameX s s' gs) : OutX s' k np fp rp :=
  ⟨out.hrp, out.sepF, out.sepN, h.wr ▸ out.rP⟩

/-- `t`'s `k` words in the frame, and its top bit `c` above them. -/
def tt (M : Mem) (fp : Addr) (k : Nat) (c : Bool) (i : Nat) : BitVec 64 :=
  if i < k then tw M fp i else (BitVec.ofBool c).setWidth 64

/-! ## The subtraction -/

/-- The subtraction's loop from word `j`: `t - n`'s words below `j` in `rp`, and the borrow into word `j`. -/
structure XSubInv (s₁ s : S) (k : Nat) (np fp rp : Addr) (t n : Nat → BitVec 64) (j : Nat) : Prop where
  j4 : j % 4 = 0
  frame : Frame s₁ s [.rax, .rbx, .rcx, .rdi, .r11, .r12, .r13, .r14]
  rbx : s.vg.gpr .rbx = wa fp (j + 8)
  rcx : s.vg.gpr .rcx = wa np j
  rdi : s.vg.gpr .rdi = wa rp j
  rax : s.vg.gpr .rax = BitVec.ofNat 64 ((k - j) / 4)
  cf : s.vg.cf = some (borrow t n j)
  agree : Agree s₁.vg.mem s.vg.mem rp j
  words : ∀ i < j, s.vg.mem.readW (wa rp i) 64 = diff t n i

set_option maxHeartbeats 4000000 in
theorem xsub_step (s₁ : S) (k : Nat) (ap bp np fp rp : Addr) (t n : Nat → BitVec 64)
    (hk4 : k % 4 = 0) (ar : Arr s₁ k ap bp np fp) (out : OutX s₁ k np fp rp)
    (hN : ∀ i < k, s₁.vg.mem.readW (wa np i) 64 = n i) (hT : ∀ i < k, s₁.vg.mem.readW (wa fp (i + 8)) 64 = t i)
    (j : Nat) (s : S) (hI : XSubInv s₁ s k np fp rp t n j) (hR : j + 4 ≤ k) :
    ∃ s', Exec I (.block Rind.X86_64.Mulx4x.sub) s (subTrace np fp rp j) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (j + 4 < k)) ∧ XSubInv s₁ s' k np fp rp t n (j + 4) := by
  have hF := hI.frame
  have hrp := out.hrp
  have hfp := ar.hfp
  have hnp := ar.hnp
  have hk := ar.k29
  have j4 := hI.j4
  have sepF := out.sepF
  have sepN := out.sepN
  obtain ⟨d1, d2⟩ := dec_ne ((k - j) / 4) (by omega) (by omega)
  have e1 : decide (1 < (k - j) / 4) = decide (j + 4 < k) := by simp only [decide_eq_decide]; omega
  have e2 : (k - j) / 4 - 1 = (k - (j + 4)) / 4 := by omega
  obtain ⟨s', hx, obx, ocx, odi, ocf, oax, ozf, omem, oF⟩ :=
    sub_ok s j k ((k - j) / 4) ap bp np fp rp (borrow t n j) (fun i => t (i - 8)) n hR (ar.frame hF) (out.frame hF)
      hI.rbx hI.rcx hI.rdi hI.rax hI.cf
      (fun i hi => (readW_agree hI.agree (fun b hb => by simp only [wa]; rcases sepN with h | h <;> bv_omega)).trans
        (hN i hi))
      (fun i h1 h2 => by
        rw [readW_agree hI.agree (fun b hb => by simp only [wa]; rcases sepF with h | h <;> bv_omega)]
        have := hT (i - 8) (by omega); rwa [show i - 8 + 8 = i by omega] at this)
  simp only [show j + 8 - 8 = j by omega, show j + 9 - 8 = j + 1 by omega, show j + 10 - 8 = j + 2 by omega,
    show j + 11 - 8 = j + 3 by omega] at ocf omem
  refine ⟨s', Exec.block hx, by rw [eval_ne ozf, d2, e1], ?_⟩
  have hag' : Agree s.vg.mem s'.vg.mem rp (j + 4) := by
    rw [omem]; exact (((Agree.refl _ rp j).writeW _).writeW _ |>.writeW _).writeW _
  refine ⟨by omega, hF.trans oF, obx, ocx, odi, by rw [oax, d1, e2], ocf, hI.agree.trans hag' (by omega), ?_⟩
  intro i hi
  rw [omem]
  have hw := hI.words
  rcases (by omega : i < j ∨ i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3) with h | rfl | rfl | rfl | rfl
  · rw [readW_wa_ne _ hrp (by omega) (by omega) (by omega), readW_wa_ne _ hrp (by omega) (by omega) (by omega),
      readW_wa_ne _ hrp (by omega) (by omega) (by omega), readW_wa_ne _ hrp (by omega) (by omega) (by omega)]
    exact hw i h
  · rw [readW_wa_ne _ hrp (by omega) (by omega) (by omega), readW_wa_ne _ hrp (by omega) (by omega) (by omega),
      readW_wa_ne _ hrp (by omega) (by omega) (by omega), readW_writeW_self]; rfl
  · rw [readW_wa_ne _ hrp (by omega) (by omega) (by omega), readW_wa_ne _ hrp (by omega) (by omega) (by omega),
      readW_writeW_self]; rfl
  · rw [readW_wa_ne _ hrp (by omega) (by omega) (by omega), readW_writeW_self]; rfl
  · rw [readW_writeW_self]; rfl

/-- The subtraction's trace. -/
def subLoopTrace (np fp rp : Addr) (k : Nat) : List Leak := loopTrace (subTrace np fp rp) 4 0 (k / 4 - 1)

/-! ## The selection -/

theorem sub32_ne (m : Nat) (h : 4 ≤ m) (h' : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 (8 * m) - 32#64 = BitVec.ofNat 64 (8 * (m - 4)) ∧
      (!(BitVec.ofNat 64 (8 * m) - 32#64 == 0)) = decide (4 < m) := by
  have e : BitVec.ofNat 64 (8 * m) - 32#64 = BitVec.ofNat 64 (8 * (m - 4)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine ⟨e, ?_⟩
  rw [e]
  by_cases h4 : 4 < m
  · have h0 : (BitVec.ofNat 64 (8 * (m - 4)) == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h''; have := congrArg BitVec.toNat h''; simp at this; omega
    rw [h0]; simp [h4]
  · have h0 : (BitVec.ofNat 64 (8 * (m - 4)) == 0) = true := by rw [show m - 4 = 0 by omega]; rfl
    rw [h0]; simp [h4]

/-- `copy`'s selection: `t`'s 16 bytes where the mask is set, else `rp`'s. -/
theorem select128x (mk : BitVec 64) (h : mk = 0 ∨ mk = -1) (T R : BitVec 128) :
    XBinOp.eval .por (XBinOp.eval .pand R (XBinOp.eval .pcmpeqd 0 (shufDwords ((0 : BitVec 64) ++ mk) 0)))
      (XBinOp.eval .pand T (shufDwords ((0 : BitVec 64) ++ mk) 0)) = if mk = 0 then R else T := by
  rcases h with rfl | rfl
  · have h1 : shufDwords ((0 : BitVec 64) ++ (0 : BitVec 64)) 0 = 0 := by decide
    have h2 : XBinOp.eval .pcmpeqd (0 : BitVec 128) 0 = -1 := pcmpeqd_self 0
    rw [h1, h2]; simp only [XBinOp.eval, ↓reduceIte]; bv_decide
  · have h1 : shufDwords ((0 : BitVec 64) ++ (-1 : BitVec 64)) 0 = -1 := by decide
    have h2 : XBinOp.eval .pcmpeqd (0 : BitVec 128) (-1) = 0 := by decide
    rw [h1, h2]
    simp only [XBinOp.eval, show ((-1 : BitVec 64) = 0) = False by decide, ↓reduceIte]; bv_decide

/-- The copy's loop from word `j`: `w`'s words below `j` in `rp`, and `t` and `rp` from `j` on as they were. -/
structure XCopyInv (s₀ s : S) (k : Nat) (fp rp : Addr) (w : Nat → BitVec 64) (j : Nat) : Prop where
  j4 : j % 4 = 0
  frame : FrameX s₀ s [.rbx, .rdi, .rdx]
  x0 : s.vg.xmm .xmm0 = 0
  x1 : s.vg.xmm .xmm1 = s₀.vg.xmm .xmm1
  rbx : s.vg.gpr .rbx = wa fp (j + 8)
  rdi : s.vg.gpr .rdi = wa rp j
  rdx : s.vg.gpr .rdx = BitVec.ofNat 64 (8 * (k - j))
  agree : ∀ y, 8 * j ≤ (y - wa fp 8).toNat → 8 * j ≤ (y - rp).toNat → s.vg.mem y = s₀.vg.mem y
  words : ∀ i < j, s.vg.mem.readW (wa rp i) 64 = w i

set_option maxHeartbeats 4000000 in
theorem xcopy_step (s₀ : S) (k : Nat) (ap bp np fp rp : Addr) (t n : Nat → BitVec 64)
    (hk4 : k % 4 = 0) (ar : Arr s₀ k ap bp np fp) (out : OutX s₀ k np fp rp) (al : fp.toNat % 16 = 0)
    (hmask : mask t n k = 0 ∨ mask t n k = -1)
    (h1 : s₀.vg.xmm .xmm1 = shufDwords ((0 : BitVec 64) ++ mask t n k) 0)
    (hT : ∀ i < k, s₀.vg.mem.readW (wa fp (i + 8)) 64 = t i)
    (hD : ∀ i < k, s₀.vg.mem.readW (wa rp i) 64 = diff t n i)
    (j : Nat) (s : S) (hI : XCopyInv s₀ s k fp rp (select t n k) j) (hR : j + 4 ≤ k) :
    ∃ s', Exec I (.block Rind.X86_64.Mulx4x.copy) s (copyTrace fp rp j) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (j + 4 < k)) ∧
      XCopyInv s₀ s' k fp rp (select t n k) (j + 4) := by
  have hF := hI.frame
  have hrp := out.hrp
  have hfp := ar.hfp
  have hk := ar.k29
  have sepF := out.sepF
  have j4 := hI.j4
  have al0 : (wa fp (j + 8)).toNat % 16 = 0 := by rw [wa_toNat (k := k + 9) hfp (by omega)]; omega
  have al1 : (wa fp (j + 10)).toNat % 16 = 0 := by rw [wa_toNat (k := k + 9) hfp (by omega)]; omega
  obtain ⟨s', hx, o0, o1, obx, odi, odx, ozf, omem, oF⟩ :=
    copy_ok s j k (8 * (k - j)) ap bp np fp rp hR (ar.frameX hF) (out.frameX hF) al0 al1 hI.rbx hI.rdi hI.rdx
  obtain ⟨e1, e2⟩ := sub32_ne (k - j) (by omega) (by omega)
  refine ⟨s', Exec.block hx, ?_, ?_⟩
  · rw [eval_ne ozf, e2]; congr 1; simp only [decide_eq_decide]; omega
  -- Words of `t` and `rp` from `j` on read as they were.
  have rdT : ∀ i, j ≤ i → i < k → s.vg.mem.readW (wa fp (i + 8)) 64 = t i := fun i h1 h2 => by
    rw [← hT i h2]; simp only [Mem.readW]; congr 1; apply read_congr; intro b hb
    apply hI.agree <;> simp only [wa] <;> rcases sepF with h | h <;> bv_omega
  have rdR : ∀ i, j ≤ i → i < k → s.vg.mem.readW (wa rp i) 64 = diff t n i := fun i h1 h2 => by
    rw [← hD i h2]; simp only [Mem.readW]; congr 1; apply read_congr; intro b hb
    apply hI.agree <;> simp only [wa] <;> rcases sepF with h | h <;> bv_omega
  have sel : ∀ R T : BitVec 128, XBinOp.eval .por
      (XBinOp.eval .pand R (XBinOp.eval .pcmpeqd (s.vg.xmm .xmm0) (s.vg.xmm .xmm1)))
      (XBinOp.eval .pand T (s.vg.xmm .xmm1)) = if mask t n k = 0 then R else T := fun R T => by
    rw [hI.x0, hI.x1, h1]; exact select128x _ hmask _ _
  have selW : ∀ i, j ≤ i → i + 1 < k →
      (if mask t n k = 0 then s.vg.mem.readW (wa rp i) 128 else s.vg.mem.readW (wa fp (i + 8)) 128).setWidth 64 =
        select t n k i ∧
      (if mask t n k = 0 then s.vg.mem.readW (wa rp i) 128 else
        s.vg.mem.readW (wa fp (i + 8)) 128).extractLsb' 64 64 = select t n k (i + 1) := by
    intro i h1 h2
    by_cases hm : mask t n k = 0
    · simp only [hm, select, ↓reduceIte, readW128_lo, readW128_hi, ← wa_succ]
      exact ⟨rdR i h1 (by omega), rdR (i + 1) (by omega) h2⟩
    · simp only [hm, select, ↓reduceIte, readW128_lo, readW128_hi, ← wa_succ]
      refine ⟨rdT i h1 (by omega), ?_⟩
      rw [show i + 8 + 1 = i + 1 + 8 by omega]; exact rdT (i + 1) (by omega) h2
  have sepRF : ∀ i, i < k → ∀ j', j' + 2 ≤ k + 9 →
      128 / 8 ≤ (wa rp i - wa fp j').toNat ∧ 64 / 8 ≤ (wa fp j' - wa rp i).toNat := fun i hi j' hj' =>
    disj_wa hrp hfp hi hj' (by rcases sepF with h | h <;> omega)
  refine ⟨by omega, hF.trans oF, by rw [o0]; exact pxor_self _, by rw [o1, hI.x1], obx, odi,
    by rw [odx, e1, show k - j - 4 = k - (j + 4) by omega], ?_, ?_⟩
  · intro y hy1 hy2
    have := (y - wa fp 8).isLt
    have := (y - rp).isLt
    rw [omem]
    simp only [Mem.writeW]
    rw [write_other _ _ 16 _ _ (by simp only [wa] at hy1 hy2 ⊢; bv_omega),
      write_other _ _ 16 _ _ (by simp only [wa] at hy1 hy2 ⊢; bv_omega),
      write_other _ _ 16 _ _ (by simp only [wa] at hy1 hy2 ⊢; bv_omega),
      write_other _ _ 16 _ _ (by simp only [wa] at hy1 hy2 ⊢; bv_omega)]
    exact hI.agree y (by omega) (by omega)
  · intro i hi
    rw [omem]
    have hw := hI.words
    obtain ⟨f0, f1⟩ := selW j le_rfl (by omega)
    obtain ⟨f2, f3⟩ := selW (j + 2) (by omega) (by omega)
    rw [show j + 2 + 8 = j + 10 by omega] at f2 f3
    rcases (by omega : i < j ∨ i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3) with h | rfl | rfl | rfl | rfl
    · rw [readW_writeW_disj _ _ _ _ _ (disj_wa hrp hrp (by omega) (by omega) (by omega)),
        readW_writeW_disj _ _ _ _ _ (disj_wa hrp hrp (by omega) (by omega) (by omega)),
        readW_writeW_disj _ _ _ _ _ (sepRF i (by omega) _ (by omega)),
        readW_writeW_disj _ _ _ _ _ (sepRF i (by omega) _ (by omega))]
      exact hw i h
    · rw [readW_writeW_disj _ _ _ _ _ (disj_wa hrp hrp (by omega) (by omega) (by omega)), readW_writeW128_lo,
        sel, f0]
    · rw [readW_writeW_disj _ _ _ _ _ (disj_wa hrp hrp (by omega) (by omega) (by omega)), wa_succ rp j,
        readW_writeW128_hi, sel, f1]
    · rw [readW_writeW128_lo, sel, f2]
    · rw [show j + 3 = j + 2 + 1 by rfl, wa_succ rp (j + 2), readW_writeW128_hi, sel, f3]

/-- The copy's trace. -/
def copyLoopTrace (fp rp : Addr) (k : Nat) : List Leak := loopTrace (copyTrace fp rp) 4 0 (k / 4 - 1)

/-! ## The phase -/

theorem tt_mask (M : Mem) (fp : Addr) (k : Nat) (c : Bool) (n : Nat → BitVec 64) :
    mask (tt M fp k c) n k =
      (BitVec.ofBool c).setWidth 64 - 0 - (BitVec.ofBool (borrow (tt M fp k c) n k)).setWidth 64 := by
  simp only [mask, tt, Nat.lt_irrefl, ↓reduceIte]

theorem val_tt (M : Mem) (fp : Addr) (k : Nat) (c : Bool) :
    val (tt M fp k c) (k + 1) = val (tw M fp) k + 2 ^ (64 * k) * c.toNat := by
  show val (tt M fp k c) k + (tt M fp k c k).toNat * 2 ^ (64 * k) = _
  rw [show val (tt M fp k c) k = val (tw M fp) k from gsum_congr fun i hi => by simp only [tt, hi, ↓reduceIte]]
  simp only [tt, Nat.lt_irrefl, ↓reduceIte, ofBool_toNat]
  ring

set_option maxHeartbeats 4000000 in
/-- `final`, the loop of `sub`, `subTail`, and the loop of `copy`: `rp` is `a·b/2^(64k) mod n`. -/
theorem finalPhase_ok (s₀ s : S) (k : Nat) (ap bp np fp rp sp0 n0' : Addr) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arr s₀ k ap bp np fp) (out : OutX s₀ k np fp rp)
    (sl : Slots s₀.vg.mem k bp fp rp sp0 n0') (al : fp.toNat % 16 = 0) (hrsp : s₀.vg.gpr .rsp = fp)
    (hN : ∀ i < k, s₀.vg.mem.readW (wa np i) 64 = n i) (hlt : val a k < val n k)
    (hI : OInv s₀ s k ap bp np fp a bw n k) :
    ∃ s₁ s₂ s₃ s₄, Exec I (.block Rind.X86_64.Mulx4x.final) s (finalTrace fp) s₁ ∧
      Exec I (.loop (.block Rind.X86_64.Mulx4x.sub) (Rind.X86_64.Cond.vg .ne)) s₁ (subLoopTrace np fp rp k) s₂ ∧
      Exec I (.block Rind.X86_64.Mulx4x.subTail) s₂ (subTailTrace fp) s₃ ∧
      Exec I (.loop (.block Rind.X86_64.Mulx4x.copy) (Rind.X86_64.Cond.vg .ne)) s₃ (copyLoopTrace fp rp k) s₄ ∧
      s₄.vg.gpr .rbx = wa fp (k + 8) ∧ s₄.vg.gpr .rdx = 0 ∧ s₄.vg.gpr .rsi = sp0 ∧
      FrameX s₀ s₄ allButSp ∧
      (∀ y, 8 * k ≤ (y - rp).toNat → 8 * (k + 9) ≤ (y - fp).toNat → s₄.vg.mem y = s₀.vg.mem y) ∧
      val (fun i => s₄.vg.mem.readW (wa rp i) 64) k < val n k ∧
      val (fun i => s₄.vg.mem.readW (wa rp i) 64) k * 2 ^ (64 * k) % val n k =
        val a k * val bw k % val n k := by
  obtain ⟨hF, hax, hdi, hsi, hcx, hbx, hkeep, c, h15, hV, Q, hQ⟩ := hI
  have hfp := ar.hfp
  have hrp := out.hrp
  have hnp := ar.hnp
  have hk := ar.k29
  have sepF := out.sepF
  have sepN := out.sepN
  have sl1 := sl.keep hkeep hfp
  have g : ∀ r, r ∉ allButSp → s.vg.gpr r = s₀.vg.gpr r := hF.gpr
  -- `final`.
  obtain ⟨s₁, hx1, p_bx, p_cx, p_15, p_dx, p_ax, p_di, p_cf, pmem, pF⟩ :=
    final_ok s k ap bp np fp rp c hk4 (ar.frame hF) ((g .rsp (by decide)).trans hrsp) hcx hax h15 sl1.s4
  let t := tt s.vg.mem fp k c
  have ar1 := (ar.frame hF).frame pF
  have out1 := (out.frame hF).frame pF
  have hT1 : ∀ i < k, s₁.vg.mem.readW (wa fp (i + 8)) 64 = t i := fun i hi => by
    rw [pmem]; simp only [t, tt, hi, ↓reduceIte]
  have hN1 : ∀ i < k, s₁.vg.mem.readW (wa np i) 64 = n i := fun i hi => by
    rw [pmem]; exact (hkeep.arr hfp ar.hnp ar.sepN hi).trans (hN i hi)
  -- The loop of `sub`.
  have hI1 : XSubInv s₁ s₁ k np fp rp t n 0 :=
    ⟨rfl, Frame.refl _ _, p_bx, by rw [p_cx, wa_zero], by rw [p_di, wa_zero],
      by rw [p_ax]; congr 1; omega, p_cf, Agree.refl _ _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨s₂, hx2, hI2⟩ := loop_ok (body := .block Rind.X86_64.Mulx4x.sub) (c := Rind.X86_64.Cond.vg .ne)
    (fun j s' => XSubInv s₁ s' k np fp rp t n j) (fun j => j + 4 ≤ k) (fun j => decide (j + 4 < k))
    (subTrace np fp rp) 4
    (fun j s' hI hR => xsub_step s₁ k ap bp np fp rp t n hk4 ar1 out1 hN1 hT1 j s' hI hR)
    (k / 4 - 1) 0 s₁ hI1 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 0 + 4 * (k / 4 - 1 + 1) = k by omega] at hI2
  have F2 := hI2.frame
  -- Words outside `rp` read as they did before the subtraction.
  have rd2 : ∀ x : Addr, (∀ b < 8, 8 * k ≤ (x + BitVec.ofNat 64 b - rp).toNat) →
      s₂.vg.mem.readW x 64 = s₁.vg.mem.readW x 64 := fun x hx => readW_agree hI2.agree hx
  have h5 : s₂.vg.mem.readW (wa fp 5) 64 = sp0 := by
    rw [rd2 _ (fun b hb => by simp only [wa]; rcases sepF with h | h <;> bv_omega), pmem]; exact sl1.s5
  -- `subTail`.
  obtain ⟨s₃, hx3, o15, obx, odi, osi, ox1, ox0, omem, oF⟩ :=
    subTail_ok s₂ k ap bp np fp rp sp0 c (borrow t n k) (ar1.frame F2)
      ((F2.gpr .rsp (by decide)).trans ((pF.gpr .rsp (by decide)).trans ((g .rsp (by decide)).trans hrsp)))
      ((F2.gpr .r15 (by decide)).trans p_15) hI2.cf hI2.rdi ((F2.gpr .rdx (by decide)).trans p_dx) h5
  rw [← tt_mask] at o15 ox1
  -- The arithmetic.
  have hpos : 0 < val n k := by omega
  have hVt : val t (k + 1) < 2 * val n k := by rw [val_tt]; omega
  obtain ⟨hm, hsl, hsm⟩ := select_nat t n k hpos hVt
  -- The loop of `copy`.
  have ar3 := (ar1.frame F2).frameX oF
  have out3 := (out1.frame F2).frameX oF
  have hT3 : ∀ i < k, s₃.vg.mem.readW (wa fp (i + 8)) 64 = t i := fun i hi => by
    rw [omem, rd2 _ (fun b hb => by simp only [wa]; rcases sepF with h | h <;> bv_omega)]; exact hT1 i hi
  have hD3 : ∀ i < k, s₃.vg.mem.readW (wa rp i) 64 = diff t n i := fun i hi => by
    rw [omem]; exact hI2.words i hi
  have hI3 : XCopyInv s₃ s₃ k fp rp (select t n k) 0 :=
    ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, by rw [ox0]; exact pxor_self _, rfl, obx, by rw [odi, wa_zero],
      by rw [oF.gpr .rdx (by decide), F2.gpr .rdx (by decide), p_dx, Nat.sub_zero], fun _ _ _ => rfl,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨s₄, hx4, hI4⟩ := loop_ok (body := .block Rind.X86_64.Mulx4x.copy) (c := Rind.X86_64.Cond.vg .ne)
    (fun j s' => XCopyInv s₃ s' k fp rp (select t n k) j) (fun j => j + 4 ≤ k) (fun j => decide (j + 4 < k))
    (copyTrace fp rp) 4
    (fun j s' hI hR => xcopy_step s₃ k ap bp np fp rp t n hk4 ar3 out3 al hm ox1 hT3 hD3 j s' hI hR)
    (k / 4 - 1) 0 s₃ hI3 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 0 + 4 * (k / 4 - 1 + 1) = k by omega] at hI4
  have F4 := hI4.frame
  refine ⟨s₁, s₂, s₃, s₄, Exec.block hx1, hx2, Exec.block hx3, hx4, hI4.rbx,
    by rw [hI4.rdx, Nat.sub_self]; rfl, by rw [F4.gpr .rsi (by decide), osi],
    (FrameX.of hF).trans ((FrameX.of pF).mono (by decide) |>.trans ((FrameX.of F2).mono (by decide)) |>.trans
      (oF.mono (by decide)) |>.trans (F4.mono (by decide))), ?_, ?_, ?_⟩
  · intro y hy1 hy2
    have := (y - rp).isLt
    rw [hI4.agree y (by simp only [wa] at hy2 ⊢; bv_omega) hy1, omem, hI2.agree y hy1, pmem]
    exact hkeep y (by simp only [wa] at hy2 ⊢; bv_omega) (by simp only [wa] at hy2 ⊢; bv_omega)
  · rw [show val (fun i => s₄.vg.mem.readW (wa rp i) 64) k = val (select t n k) k from
      gsum_congr fun i hi => by dsimp only; rw [hI4.words i hi]]
    exact hsl
  · rw [show val (fun i => s₄.vg.mem.readW (wa rp i) 64) k = val (select t n k) k from
      gsum_congr fun i hi => by dsimp only; rw [hI4.words i hi]]
    rw [Nat.mul_mod, hsm, ← Nat.mul_mod, val_tt, Nat.mul_comm, hQ, Nat.add_mul_mod_self_right]

end rind.x86_64.mulx4x
