import Rind.X86_64.Sqrx8xMontHead
import Rind.X86_64.Sqrx8xSpec
import Rind.X86_64.Mulx4xTail

/-! # bn_sqrx8x_mont's blocks around the call, run

`setup`, which stores `n0` and the stack pointer and zeroes `t`'s last two words; the call and its return; `post`;
the four words of the subtraction `sub`; `subTail`, which makes the mask; four words of the selection `copy`; and
the epilogue. The frame is at `wsp`, the stack pointer between the walk and the epilogue: slots at words 0 to 5,
and `t`'s `2k + 2` words from word 6, so that the call's return address makes `wsp - 8` the internal routine's
frame. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8xmont

section
variable (s : VG.X86_64.State)
@[simp] theorem xmm_setXmm' (d : XReg) (v : BitVec 128) (x : XReg) :
    (s.setXmm d v).xmm x = if x = d then v else s.xmm x := rfl
end

/-- What the blocks after the walk reach: `n`'s `k` words, which they may read, `rp`'s, which they may write,
and the frame's `2k + 8` words at `wsp`; none overlaps another, and none wraps. -/
structure TArr (s : S) (k : Nat) (np rp wsp : Addr) : Prop where
  k29 : k < 2 ^ 29
  hnp : np.toNat + 8 * k ≤ 2 ^ 64
  hrp : rp.toNat + 8 * k ≤ 2 ^ 64
  hw : wsp.toNat + 8 * (2 * k + 8) ≤ 2 ^ 64
  sepN : np.toNat + 8 * k ≤ wsp.toNat ∨ wsp.toNat + 8 * (2 * k + 8) ≤ np.toNat
  sepP : rp.toNat + 8 * k ≤ wsp.toNat ∨ wsp.toNat + 8 * (2 * k + 8) ≤ rp.toNat
  sepPN : rp.toNat + 8 * k ≤ np.toNat ∨ np.toNat + 8 * k ≤ rp.toNat
  rN : ⟨np, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rP : ⟨rp, 8 * k⟩ ∈ s.vg.wr
  rF : ∃ L, 8 * (2 * k + 8) ≤ L ∧ ⟨wsp, L⟩ ∈ s.vg.wr

theorem TArr.frameX {s s' : S} {k : Nat} {np rp wsp : Addr} {gs : List Reg} (ar : TArr s k np rp wsp)
    (h : FrameX s s' gs) : TArr s' k np rp wsp := by
  obtain ⟨hk, hnp, hrp, hw, sepN, sepP, sepPN, rN, rP, rF⟩ := ar
  rw [← h.rd, ← h.wr] at rN
  rw [← h.wr] at rP rF
  exact ⟨hk, hnp, hrp, hw, sepN, sepP, sepPN, rN, rP, rF⟩

theorem TArr.frame {s s' : S} {k : Nat} {np rp wsp : Addr} {gs : List Reg} (ar : TArr s k np rp wsp)
    (h : Frame s s' gs) : TArr s' k np rp wsp := ar.frameX (FrameX.of h)

set_option hygiene false in
/-- Discharges the side conditions of a block's run: regions, accesses apart, and index bounds. -/
macro "wt_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem,
        wr_setMem, rd_setXmm, wr_setXmm]) <;>
     first
      | (refine inR (List.mem_append_right _ rF) ?_; simp only; bv_omega)
      | (refine inR (List.mem_append_right _ rP) ?_; simp only; bv_omega)
      | (refine inR rF ?_; simp only; bv_omega)
      | (refine inR rP ?_; simp only; bv_omega)
      | (refine inR rN ?_; simp only; bv_omega)
      | (unfold Apart; constructor <;> bv_omega)
      | (constructor <;> bv_omega)
      | omega)

/-- Runs a block with `wt_disch`. -/
syntax "wt_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wt_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := wt_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, store64_of, load128_of, store128_of, Rind.X86_64.exec, Rind.X86_64.addrs,
      VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, XOp.exec, execAlu, readSrc, Option.map_some, Option.bind_some,
      State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod,
      Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb, ofNat_add_add, ofNat_sub_ofNat,
      BitVec.xor_self, BitVec.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod,
      Nat.add_zero, ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero',
      ofNat_add_pos, readW_writeW_eq, readW_writeW_sep, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg,
      gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, cf_arithFlags, gpr_setFlags, mem_setFlags,
      rd_setFlags, wr_setFlags, cf_setFlags, gpr_setMem, mem_setMem, rd_setMem, wr_setMem, cf_setMem, gpr_setXmm,
      mem_setXmm, rd_setXmm, wr_setXmm, cf_setXmm, xmm_setXmm, xmm_setMem, xmm_setReg, xmm_arithFlags,
      xmm_setFlags, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append,
      List.cons_append])

/-- Closes a block lemma's conclusions: registers, flags, memory, and the frame. -/
macro "wt_close" : tactic => `(tactic| (
    repeat' apply And.intro
    all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
    all_goals try refine FrameX.mk (fun r hr => ?_) ?_ ?_ rfl
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
      others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
      mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
      others_setMem, gpr_setXmm, mem_setXmm, wr_setXmm, xmm_setXmm, others_setXmm, cf_arithFlags, cf_setReg,
      cf_setFlags, cf_setMem, cf_setXmm, zf_setReg, zf_setFlags, zf_arithFlags, zf_setMem, zf_setXmm, reduceCtorEq,
      ↓reduceIte, *]
    all_goals first
      | rfl
      | skip))

/-! ## The setup -/

theorem setWidth_zero_append (x : BitVec 64) : ((0 : BitVec 64) ++ x).setWidth 64 = x := by
  exact BitVec.setWidth_append_eq_right

theorem signExtend_32' : (32 : BitVec 32).signExtend 64 = 32#64 := by decide
theorem signExtend_40 : (40 : BitVec 32).signExtend 64 = 40#64 := by decide
theorem signExtend_48 : (48 : BitVec 32).signExtend 64 = 48#64 := by decide

theorem wa2k (p : Addr) (k : Nat) : p + BitVec.ofNat 64 (8 * k) * 2#64 + 6#64 * 8#64 = wa p (2 * k + 6) := by
  simp only [wa]
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

def setupTrace (wsp : Addr) (k : Nat) : List Leak :=
  [.addr (wa wsp 4), .addr (wa wsp 5), .addr (wa wsp (2 * k + 6))]

set_option maxHeartbeats 4000000 in
theorem setup_ok (s : S) (k : Nat) (wsp np rp sp0 n0' : Addr) (L : Nat) (rest : List Region)
    (hk : k < 2 ^ 29) (hL : 8 * (2 * k + 8) ≤ L)
    (hwr : s.vg.wr = ⟨wsp, L⟩ :: rest)
    (hrsp : s.vg.gpr .rsp = wsp) (hr9 : s.vg.gpr .r9 = 0 - BitVec.ofNat 64 (8 * k)) (hr8 : s.vg.gpr .r8 = n0')
    (hrax : s.vg.gpr .rax = sp0) (hrcx : s.vg.gpr .rcx = np) (hrdi : s.vg.gpr .rdi = rp) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.setup s = some (s', setupTrace wsp k) ∧
      s'.vg.mem = ((s.vg.mem.writeW (wa wsp 4) n0').writeW (wa wsp 5) sp0).writeW (wa wsp (2 * k + 6))
        (0 : BitVec 128) ∧
      s'.vg.gpr .r9 = BitVec.ofNat 64 (8 * k) ∧ s'.vg.gpr .r10 = 0 - BitVec.ofNat 64 (8 * k) ∧
      s'.vg.xmm .xmm0 = 0 ∧ sqrx8x.xlo s' .xmm1 = rp ∧ sqrx8x.xlo s' .xmm2 = np ∧
      sqrx8x.xlo s' .xmm3 = 0 - BitVec.ofNat 64 (8 * k) ∧
      s'.vg.wr = s.vg.wr ∧ s'.lo = s.lo ∧ others s'.vg = others s.vg ∧
      (∀ r, r ∉ [Reg.r9, .r10] → s'.vg.gpr r = s.vg.gpr r) := by
  have rF : (⟨wsp, L⟩ : Region) ∈ s.vg.wr := by rw [hwr]; exact List.mem_cons_self
  apply ex_of_eq
  · rw [execBlock_acc]
    wt_run [Rind.X86_64.Sqrx8xMont.setup, hrsp, hr9, hr8, hrax, hrcx, hrdi, zero_sub_zero_sub, signExtend_32',
      signExtend_40, signExtend_48, wa2k, pxor_self]
    rfl
  · rfl
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
    all_goals try (simp only [xmm_setXmm', xmm_setMem, reduceCtorEq, ↓reduceIte, sqrx8x.xlo, setWidth_zero_append]; done)
    all_goals try (simp only [gpr_setReg, gpr_arithFlags, gpr_setMem, gpr_setXmm, reduceCtorEq, ↓reduceIte]; done)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setMem, gpr_setXmm, hr.1, hr.2, ↓reduceIte]

/-! ## The call and its return -/

theorem call_ok (s : S) (wsp : Addr) (L : Nat) (rest : List Region) (hrsp : s.vg.gpr .rsp = wsp)
    (hwr : s.vg.wr = ⟨wsp, L⟩ :: rest) (hlo : s.lo.toNat + 8 ≤ wsp.toNat) :
    ∃ s₁, Rind.X86_64.call s = some s₁ ∧ s₁.vg.gpr .rsp = wsp - 8 ∧
      s₁.vg.wr = ⟨wsp - 8, L + 8⟩ :: rest ∧ s₁.vg.mem = s.vg.mem.writeW (wsp - 8) (s.vg.unknowns 0) ∧
      (∀ r, r ≠ .rsp → s₁.vg.gpr r = s.vg.gpr r) ∧ s₁.vg.xmm = s.vg.xmm ∧ s₁.vg.rd = s.vg.rd ∧
      s₁.vg.mxcsr = s.vg.mxcsr ∧ s₁.lo = s.lo := by
  have h8 : (wsp - 8).toNat = wsp.toNat - 8 := by
    rw [BitVec.toNat_sub]; simp only [show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hm := moveSp_down s (wsp - 8) (by rw [hwr, hrsp]; rfl) (by rw [hwr]; exact List.cons_ne_nil _ _)
    (by omega) (by rw [hrsp]; omega)
  simp only [Rind.X86_64.call, hrsp, hm, Option.bind_some, hwr, List.headD_cons, List.tail_cons]
  rw [store64_of _ (by
    simp only [gpr_setReg, gpr_setWr, wr_setWr, ↓reduceIte, h8]
    refine inR List.mem_cons_self ?_; simp only; bv_omega)]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_setMem, gpr_setWr, gpr_setReg, ↓reduceIte]
  · simp only [wr_setMem, wr_setWr, List.cons.injEq, Region.mk.injEq, true_and, and_true]; omega
  · simp only [mem_setMem, gpr_setWr, gpr_setReg, ↓reduceIte, mem_setWr, mem_setReg]
  · intro r hr; simp only [gpr_setMem, gpr_setWr, gpr_setReg, hr, ↓reduceIte]

theorem ret_ok (s₁ s₂ : S) (fp : Addr) (L : Nat) (rest : List Region) (h1 : s₁.vg.gpr .rsp = fp)
    (h2 : s₂.vg.gpr .rsp = fp) (hm : s₂.vg.mem.readW fp 64 = s₁.vg.mem.readW fp 64)
    (hwr : s₂.vg.wr = ⟨fp, L⟩ :: rest) (hL : 8 ≤ L) (hfp : fp.toNat + 8 < 2 ^ 64) :
    ∃ s', Rind.X86_64.ret s₁ s₂ = some s' ∧ s'.vg.gpr .rsp = fp + 8 ∧
      s'.vg.wr = ⟨fp + 8, L - 8⟩ :: rest ∧ s'.vg.mem = lose s₂.vg.mem fp 8 s₂.vg.unknowns ∧
      (∀ r, r ≠ .rsp → s'.vg.gpr r = s₂.vg.gpr r) ∧ s'.vg.xmm = s₂.vg.xmm ∧ s'.vg.rd = s₂.vg.rd ∧
      s'.vg.mxcsr = s₂.vg.mxcsr ∧ s'.lo = s₂.lo := by
  have h8 : (fp + 8).toNat = fp.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hu := moveSp_up s₂ (fp + 8) L rest (by rw [hwr, h2]) (by rw [h2]; omega) (by rw [h2]; omega)
  rw [h2, h8, show fp.toNat + 8 - fp.toNat = 8 by omega] at hu
  simp only [Rind.X86_64.ret, h1, h2, hm, and_self, ↓reduceIte, hu]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_setReg, ↓reduceIte]
  · intro r hr; simp only [gpr_setReg, hr, ↓reduceIte]

/-! ## After the call -/

theorem msb_neg8k (k : Nat) (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) :
    (BitVec.ofNat 64 (18446744073709551616 - 8 * k)).msb = true := by
  rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_true_eq]; omega
theorem sar5 (k : Nat) (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) (h8 : k % 8 = 0) :
    (BitVec.ofNat 64 (18446744073709551616 - 8 * k)).sshiftRight 5 = BitVec.ofNat 64 (2 ^ 64 - k / 4) := by
  rw [BitVec.sshiftRight_eq_of_msb_true (msb_neg8k k hk8 hk)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_not, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega
theorem lsb4 (k : Nat) (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) (h8 : k % 8 = 0) :
    (BitVec.ofNat 64 (18446744073709551616 - 8 * k)).getLsbD 4 = false := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  have : (18446744073709551616 - 8 * k) / 16 % 2 = 0 := by omega
  simp only [Nat.reduceSub, Nat.reducePow, this]
  decide
theorem post_rbx (p : Addr) (k : Nat) (hk : k < 2 ^ 29) :
    wa (p - 8#64) (2 * k + 7) + BitVec.ofNat 64 (18446744073709551616 - 8 * k) = wa p (k + 6) := by
  simp only [wa]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem post_ok (s : S) (k : Nat) (wsp rp : Addr) (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) (h8 : k % 8 = 0)
    (hr8 : s.vg.gpr .r8 = wa (wsp - 8#64) (2 * k + 7)) (hrcx : s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 * k))
    (hx1 : sqrx8x.xlo s .xmm1 = rp) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.post s = some (s', []) ∧
      s'.vg.gpr .rbx = wa wsp (k + 6) ∧ s'.vg.gpr .r9 = BitVec.ofNat 64 (2 ^ 64 - 8 * k) ∧
      s'.vg.gpr .rdx = BitVec.ofNat 64 (2 ^ 64 - 8 * k) ∧ s'.vg.gpr .rdi = rp ∧
      s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - k / 4) ∧ s'.vg.cf = some false ∧ s'.vg.mem = s.vg.mem ∧
      Frame s s' [.rbx, .rcx, .rdx, .rdi, .r9] := by
  simp only [sqrx8x.xlo] at hx1
  apply ex_of_eq
  · rw [execBlock_acc]
    reg_run [Rind.X86_64.Sqrx8xMont.post, hr8, hrcx, hx1, mul_ofNat_one, post_rbx (wsp) k hk, sar5 k hk8 hk h8,
      lsb4 k hk8 hk h8, Nat.reduceLeDiff, and_self, sqrx8x.extract_lo, gpr_setFlags, cf_setFlags, xmm_setReg]
    rfl
  · rfl
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ↓reduceIte]

/-- `inc`'s flags, folded. -/
theorem exec_inc (d : Reg) (s : S) : Rind.X86_64.exec (.inc d) s =
    some { s with vg := (s.vg.setFlags s.vg.cf (some (addOverflow (s.vg.gpr d) 1 (s.vg.gpr d + 1)))
      (some (s.vg.gpr d + 1 == 0)) (some (s.vg.gpr d + 1).msb)).setReg d (s.vg.gpr d + 1) } := rfl

def subTrace (np rp wsp : Addr) (b j : Nat) : List Leak :=
  [.addr (wa wsp b), .addr (wa wsp (b + 1)), .addr (wa wsp (b + 2)), .addr (wa wsp (b + 3)),
   .addr (wa np j), .addr (wa np (j + 1)), .addr (wa np (j + 2)), .addr (wa np (j + 3)),
   .addr (wa rp j), .addr (wa rp (j + 1)), .addr (wa rp (j + 2)), .addr (wa rp (j + 3))]

set_option maxHeartbeats 8000000 in
theorem sub_ok (s : S) (j k b : Nat) (np rp wsp x : Addr) (c : Bool) (T n : Nat → BitVec 64)
    (hjk : j + 4 ≤ k) (hb : k + 6 ≤ b) (hb' : b + 4 ≤ 2 * k + 8) (ar : TArr s k np rp wsp)
    (hrbx : s.vg.gpr .rbx = wa wsp b) (hrbp : s.vg.gpr .rbp = wa np j) (hrdi : s.vg.gpr .rdi = wa rp j)
    (hrcx : s.vg.gpr .rcx = x) (hcf : s.vg.cf = some c)
    (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i, b ≤ i → i < b + 4 → s.vg.mem.readW (wa wsp i) 64 = T i) :
    let y0 := T b - n j - (BitVec.ofBool c).setWidth 64
    let b1 := decide ((T b).toNat < (n j).toNat + c.toNat)
    let y1 := T (b + 1) - n (j + 1) - (BitVec.ofBool b1).setWidth 64
    let b2 := decide ((T (b + 1)).toNat < (n (j + 1)).toNat + b1.toNat)
    let y2 := T (b + 2) - n (j + 2) - (BitVec.ofBool b2).setWidth 64
    let b3 := decide ((T (b + 2)).toNat < (n (j + 2)).toNat + b2.toNat)
    let y3 := T (b + 3) - n (j + 3) - (BitVec.ofBool b3).setWidth 64
    let b4 := decide ((T (b + 3)).toNat < (n (j + 3)).toNat + b3.toNat)
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.sub s = some (s', subTrace np rp wsp b j) ∧
      s'.vg.gpr .rbx = wa wsp (b + 4) ∧ s'.vg.gpr .rbp = wa np (j + 4) ∧ s'.vg.gpr .rdi = wa rp (j + 4) ∧
      s'.vg.cf = some b4 ∧ s'.vg.gpr .rcx = x + 1 ∧ s'.vg.zf = some (x + 1 == 0) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa rp j) y0).writeW (wa rp (j + 1)) y1).writeW (wa rp (j + 2)) y2).writeW
        (wa rp (j + 3)) y3 ∧
      Frame s s' [.rbx, .rbp, .rdi, .rcx, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hnp, hrp, hw, sepN, sepP, sepPN, rN, rP, LF, hLF, rF⟩ := ar
  intro y0 b1 y1 b2 y2 b3 y3 b4
  apply ex_of_eq
  · rw [execBlock_acc]
    wt_run [Rind.X86_64.Sqrx8xMont.sub, hrbx, hrbp, hrdi, hrcx, hcf, hN, hT, exec_inc]
    rfl
  · rfl
  · wt_close

theorem wa_negk (p : Addr) (n k : Nat) (h : k ≤ n) (hk : k < 2 ^ 60) :
    wa p n + BitVec.ofNat 64 (18446744073709551616 - 8 * k) = wa p (n - k) := by
  simp only [wa]
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

def subTailTrace (wsp : Addr) : List Leak := [.addr (wa wsp 5)]

set_option maxHeartbeats 4000000 in
theorem subTail_ok (s : S) (k : Nat) (np rp wsp sp0 : Addr) (c b : Bool) (ar : TArr s k np rp wsp)
    (hrsp : s.vg.gpr .rsp = wsp) (hrax : s.vg.gpr .rax = (BitVec.ofBool c).setWidth 64) (hcf : s.vg.cf = some b)
    (hrbx : s.vg.gpr .rbx = wa wsp (2 * k + 6)) (hrdi : s.vg.gpr .rdi = wa rp k)
    (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (2 ^ 64 - 8 * k)) (h5 : s.vg.mem.readW (wa wsp 5) 64 = sp0) :
    let mk := (BitVec.ofBool c).setWidth 64 - 0 - (BitVec.ofBool b).setWidth 64
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.subTail s = some (s', subTailTrace wsp) ∧
      s'.vg.gpr .rax = mk ∧ s'.vg.gpr .rbx = wa wsp (k + 6) ∧ s'.vg.gpr .rdi = rp ∧ s'.vg.gpr .rsi = sp0 ∧
      s'.vg.xmm .xmm1 = shufDwords ((0 : BitVec 64) ++ mk) 0 ∧
      s'.vg.xmm .xmm0 = 0 ∧ s'.vg.mem = s.vg.mem ∧ FrameX s s' [.rax, .rbx, .rdi, .rsi] := by
  obtain ⟨hk, hnp, hrp, hw, sepN, sepP, sepPN, rN, rP, LF, hLF, rF⟩ := ar
  intro mk
  apply ex_of_eq
  · rw [execBlock_acc]
    wt_run [Rind.X86_64.Sqrx8xMont.subTail, hrsp, hrax, hcf, hrbx, hrdi, hr9, h5, mul_ofNat_one, pxor_self,
      wa_negk wsp (2 * k + 6) k (by omega) (by omega), wa_negk rp k k le_rfl (by omega), Nat.sub_self, wa_zero,
      show 2 * k + 6 - k = k + 6 by omega]
    rfl
  · rfl
  · wt_close

/-- `a` is 16-byte aligned, as `movdqa` requires; a definition, which `omega` does not unfold, so that a block's
side conditions do not case split on it. -/
def Al16 (a : Addr) : Prop := a.toNat % 16 = 0

theorem Al16.eq {a : Addr} (h : Al16 a) : a.toNat % 16 = 0 := h

theorem negk_div (k : Nat) (hk : k < 2 ^ 60) : (18446744073709551616 - (18446744073709551616 - 8 * k)) / 8 = k := by
  omega

theorem ofNat_sub4 (n k : Nat) (h : k ≤ n) (hn : n < 2 ^ 60) :
    BitVec.ofNat 64 (n + 4) - BitVec.ofNat 64 k - 4#64 = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem ofNat_sub2 (n k : Nat) (h : k ≤ n) (hn : n < 2 ^ 60) :
    BitVec.ofNat 64 (n + 4) - BitVec.ofNat 64 k - 2#64 = BitVec.ofNat 64 (n - k + 2) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

def copyTrace (rp wsp : Addr) (b k j : Nat) : List Leak :=
  [.addr (wa wsp b), .addr (wa wsp (b + 2)), .addr (wa rp j), .addr (wa rp (j + 2)), .addr (wa wsp b),
   .addr (wa wsp (b + 2)), .addr (wa wsp (b - k)), .addr (wa wsp (b - k + 2)), .addr (wa rp j),
   .addr (wa rp (j + 2))]

set_option maxHeartbeats 8000000 in
theorem copy_ok (s : S) (j k b : Nat) (np rp wsp x : Addr)
    (hjk : j + 4 ≤ k) (hb : k + 6 ≤ b) (hb' : b + 4 ≤ 2 * k + 8) (ar : TArr s k np rp wsp)
    (al0 : Al16 (wa wsp b)) (al1 : Al16 (wa wsp (b + 2))) (al2 : Al16 (wa wsp (b - k)))
    (al3 : Al16 (wa wsp (b - k + 2)))
    (hrbx : s.vg.gpr .rbx = wa wsp b) (hrdi : s.vg.gpr .rdi = wa rp j)
    (hrdx : s.vg.gpr .rdx = BitVec.ofNat 64 (2 ^ 64 - 8 * k)) (hr9 : s.vg.gpr .r9 = x) :
    let M := s.vg.mem
    let x0 := s.vg.xmm .xmm0
    let x1 := s.vg.xmm .xmm1
    let z := XBinOp.eval .pcmpeqd x0 x1
    let y0 := XBinOp.eval .por (XBinOp.eval .pand (M.readW (wa rp j) 128) z)
      (XBinOp.eval .pand (M.readW (wa wsp b) 128) x1)
    let y1 := XBinOp.eval .por (XBinOp.eval .pand (M.readW (wa rp (j + 2)) 128) z)
      (XBinOp.eval .pand (M.readW (wa wsp (b + 2)) 128) x1)
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.copy s = some (s', copyTrace rp wsp b k j) ∧
      s'.vg.xmm .xmm0 = XBinOp.eval .pxor z z ∧ s'.vg.xmm .xmm1 = x1 ∧
      s'.vg.gpr .rbx = wa wsp (b + 4) ∧ s'.vg.gpr .rdi = wa rp (j + 4) ∧
      s'.vg.gpr .r9 = x + 32#64 ∧ s'.vg.zf = some (x + 32#64 == 0) ∧
      s'.vg.mem = (((((M.writeW (wa wsp b) x0).writeW (wa wsp (b + 2)) x0).writeW (wa wsp (b - k)) x0).writeW
        (wa wsp (b - k + 2)) x0).writeW (wa rp j) y0).writeW (wa rp (j + 2)) y1 ∧
      FrameX s s' [.rbx, .rdi, .r9] := by
  obtain ⟨hk, hnp, hrp, hw, sepN, sepP, sepPN, rN, rP, LF, hLF, rF⟩ := ar
  intro M x0 x1 z y0 y1
  apply ex_of_eq
  · rw [execBlock_acc]
    wt_run [Rind.X86_64.Sqrx8xMont.copy, hrbx, hrdi, hrdx, hr9, al0.eq, al1.eq, al2.eq, al3.eq, signExtend_32, mul_ofNat_one,
      negk_div k (by omega), ofNat_sub4 b k (by omega) (by omega), ofNat_sub2 b k (by omega) (by omega)]
    rfl
  · rfl
  · wt_close

def epilogueTrace (sp0 : Addr) : List Leak :=
  [.addr (sp0 - 48#64), .addr (sp0 - 40#64), .addr (sp0 - 32#64), .addr (sp0 - 24#64), .addr (sp0 - 16#64),
   .addr (sp0 - 8#64)]

set_option maxHeartbeats 4000000 in
theorem epilogue_ok (s : S) (n : Nat) (wsp sp0 v15 v14 v13 v12 vbp vbx : Addr) (rest : List Region)
    (hfp : wsp.toNat + 48 ≤ sp0.toNat)
    (hrsp : s.vg.gpr .rsp = wsp) (hrsi : s.vg.gpr .rsi = sp0)
    (hwr : s.vg.wr = ⟨wsp, n⟩ :: rest) (hn : n = sp0.toNat + 8 - wsp.toNat)
    (h15 : s.vg.mem.readW (sp0 - 48#64) 64 = v15)
    (h14 : s.vg.mem.readW (sp0 - 40#64) 64 = v14) (h13 : s.vg.mem.readW (sp0 - 32#64) 64 = v13)
    (h12 : s.vg.mem.readW (sp0 - 24#64) 64 = v12) (hbp : s.vg.mem.readW (sp0 - 16#64) 64 = vbp)
    (hbx : s.vg.mem.readW (sp0 - 8#64) 64 = vbx) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.epilogue s = some (s', epilogueTrace sp0) ∧
      s'.vg.gpr .rsp = sp0 ∧ s'.vg.gpr .rax = 1 ∧ s'.vg.gpr .r15 = v15 ∧ s'.vg.gpr .r14 = v14 ∧
      s'.vg.gpr .r13 = v13 ∧ s'.vg.gpr .r12 = v12 ∧ s'.vg.gpr .rbp = vbp ∧ s'.vg.gpr .rbx = vbx ∧
      s'.vg.wr = ⟨sp0, 8⟩ :: rest ∧ s'.vg.rd = s.vg.rd ∧ s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo ∧
      s'.vg.mem = lose s.vg.mem wsp (sp0.toNat - wsp.toNat) s.vg.unknowns := by
  have rS : (⟨wsp, n⟩ : Region) ∈ s.vg.wr := by rw [hwr]; exact List.mem_cons_self
  apply ex_of_eq
  · rw [execBlock_acc]
    simp (config := { maxSteps := 4000000 }) (disch := xepi_disch) only [Rind.X86_64.Sqrx8xMont.epilogue, hrsp,
      hrsi, execAcc_cons, execAcc_nil, load64_of, Rind.X86_64.exec, Rind.X86_64.addrs,
      VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, readSrc, Option.map_some, Option.bind_some, State.ea,
      Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat,
      Int.reducePow, ea_pos, ea_comb, ofNat_add_pos, disp_neg, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv,
      Nat.reducePow, ofNat_zero, add_zero', signExtend_one, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append, List.cons_append,
      h15, h14, h13, h12, hbp, hbx]
    rw [moveSp_up _ _ n rest (by simp only [wr_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp, hwr])
      (by simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp]; omega)
      (by simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp]; omega)]
    rfl
  · rfl
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp, hn]
    repeat' apply And.intro
    all_goals first | trivial | rfl | (congr 2; omega)

end rind.x86_64.sqrx8xmont
