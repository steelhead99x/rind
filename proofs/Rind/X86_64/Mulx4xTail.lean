import Rind.X86_64.Mulx4xAsm
import Rind.X86_64.Mul4xFinal

/-! # bn_mulx4x_mont's last blocks, run

`final`, which takes the top bit and starts subtracting `n` from `t` into `rp`; the four words of the
subtraction `sub`; `subTail`, which makes the mask; four words of the selection `copy`; and the epilogue. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mulx4x

/-- Where `rp` lies: `k` words, which the routine may write, apart from the frame and `n`. -/
structure OutX (s : S) (k : Nat) (np fp rp : Addr) : Prop where
  hrp : rp.toNat + 8 * k ≤ 2 ^ 64
  sepF : rp.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ rp.toNat
  sepN : rp.toNat + 8 * k ≤ np.toNat ∨ np.toNat + 8 * k ≤ rp.toNat
  rP : ⟨rp, 8 * k⟩ ∈ s.vg.wr

theorem wa_sub8 (p : Addr) (k : Nat) : wa p k - BitVec.ofNat 64 (8 * k) = p := by
  simp only [wa]; bv_omega

theorem sub_sub0 (x : BitVec 64) : 0 - (0 - x) = x := by bv_omega

theorem getLsbD_8k (k : Nat) (hk4 : k % 4 = 0) : (BitVec.ofNat 64 (8 * k)).getLsbD 4 = false := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  have : 8 * k / 16 % 2 = 0 := by omega
  simp [this]

theorem signExtend_32 : (32 : BitVec 32).signExtend 64 = 32#64 := by decide

set_option hygiene false in
/-- `mulx_disch`, `rp`'s region `rP`, and accesses apart. -/
macro "xtail_disch" : tactic => `(tactic| no_recover first
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

/-- `mulx_run` with `xtail_disch` and the vector instructions. -/
syntax "xtail_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| xtail_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := xtail_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, store64_of, load128_of, store128_of, ↓exec_dec, Rind.X86_64.exec, Rind.X86_64.addrs,
      VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, XOp.exec, execAlu, readSrc, Option.map_some, Option.bind_some,
      State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod,
      Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb, ofNat_add_add, ofNat_sub_ofNat,
      BitVec.xor_self, BitVec.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod,
      Nat.add_zero, ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero',
      ofNat_add_pos, readW_writeW_eq, readW_writeW_sep, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, gpr_arithFlags,
      mem_arithFlags, rd_arithFlags, wr_arithFlags, cf_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags,
      wr_setFlags, cf_setFlags, gpr_setMem, mem_setMem, rd_setMem, wr_setMem, cf_setMem, gpr_setXmm, mem_setXmm,
      rd_setXmm, wr_setXmm, cf_setXmm, xmm_setXmm, xmm_setMem, reduceCtorEq, ↓reduceIte, List.map_nil,
      List.map_cons, List.append_nil, List.nil_append, List.cons_append])

/-- Proves a block's lemma with `xtail_run`. -/
syntax "xtail_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| xtail_block [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      xtail_run [$xs,*]
      rfl
    · rfl
    · repeat' apply And.intro
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

def finalTrace (fp : Addr) : List Leak := [.addr (wa fp 4)]

set_option maxHeartbeats 4000000 in
theorem final_ok (s : S) (k : Nat) (ap bp np fp rp : Addr) (c : Bool) (hk4 : k % 4 = 0)
    (ar : Arr s k ap bp np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrcx : s.vg.gpr .rcx = wa np k) (hrax : s.vg.gpr .rax = BitVec.ofNat 64 (8 * k))
    (hr15 : s.vg.gpr .r15 = 0 - (BitVec.ofBool c).setWidth 64) (h4 : s.vg.mem.readW (wa fp 4) 64 = rp) :
    ∃ s', execBlock I Rind.X86_64.Mulx4x.final s = some (s', finalTrace fp) ∧
      s'.vg.gpr .rbx = wa fp 8 ∧ s'.vg.gpr .rcx = np ∧ s'.vg.gpr .r15 = (BitVec.ofBool c).setWidth 64 ∧
      s'.vg.gpr .rdx = BitVec.ofNat 64 (8 * k) ∧ s'.vg.gpr .rax = BitVec.ofNat 64 (8 * k / 32) ∧
      s'.vg.gpr .rdi = rp ∧ s'.vg.cf = some false ∧ s'.vg.mem = s.vg.mem ∧
      Frame s s' [.rax, .rcx, .rdx, .rdi, .rbx, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  have h8k : 8 * k < 2 ^ 64 := by omega
  mulx_block [Rind.X86_64.Mulx4x.final, hrsp, hrcx, hrax, hr15, h4, wa_sub8, sub_sub0, execShift,
    ofNat_shr (8 * k) 5 h8k, getLsbD_8k k hk4, Nat.reduceLeDiff, and_self]

def subTrace (np fp rp : Addr) (j : Nat) : List Leak :=
  [.addr (wa fp (j + 8)), .addr (wa fp (j + 9)), .addr (wa fp (j + 10)), .addr (wa fp (j + 11)),
   .addr (wa np j), .addr (wa np (j + 1)), .addr (wa np (j + 2)), .addr (wa np (j + 3)),
   .addr (wa rp j), .addr (wa rp (j + 1)), .addr (wa rp (j + 2)), .addr (wa rp (j + 3))]

set_option maxHeartbeats 8000000 in
theorem sub_ok (s : S) (j k c : Nat) (ap bp np fp rp : Addr) (b : Bool) (T n : Nat → BitVec 64)
    (hjk : j + 4 ≤ k) (ar : Arr s k ap bp np fp) (out : OutX s k np fp rp)
    (hrbx : s.vg.gpr .rbx = wa fp (j + 8)) (hrcx : s.vg.gpr .rcx = wa np j) (hrdi : s.vg.gpr .rdi = wa rp j)
    (hrax : s.vg.gpr .rax = BitVec.ofNat 64 c) (hcf : s.vg.cf = some b)
    (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i, j + 8 ≤ i → i < j + 12 → s.vg.mem.readW (wa fp i) 64 = T i) :
    let y0 := T (j + 8) - n j - (BitVec.ofBool b).setWidth 64
    let b1 := decide ((T (j + 8)).toNat < (n j).toNat + b.toNat)
    let y1 := T (j + 9) - n (j + 1) - (BitVec.ofBool b1).setWidth 64
    let b2 := decide ((T (j + 9)).toNat < (n (j + 1)).toNat + b1.toNat)
    let y2 := T (j + 10) - n (j + 2) - (BitVec.ofBool b2).setWidth 64
    let b3 := decide ((T (j + 10)).toNat < (n (j + 2)).toNat + b2.toNat)
    let y3 := T (j + 11) - n (j + 3) - (BitVec.ofBool b3).setWidth 64
    let b4 := decide ((T (j + 11)).toNat < (n (j + 3)).toNat + b3.toNat)
    ∃ s', execBlock I Rind.X86_64.Mulx4x.sub s = some (s', subTrace np fp rp j) ∧
      s'.vg.gpr .rbx = wa fp (j + 12) ∧ s'.vg.gpr .rcx = wa np (j + 4) ∧ s'.vg.gpr .rdi = wa rp (j + 4) ∧
      s'.vg.cf = some b4 ∧ s'.vg.gpr .rax = BitVec.ofNat 64 c - 1 ∧
      s'.vg.zf = some (BitVec.ofNat 64 c - 1 == 0) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa rp j) y0).writeW (wa rp (j + 1)) y1).writeW (wa rp (j + 2)) y2).writeW
        (wa rp (j + 3)) y3 ∧
      Frame s s' [.rax, .rbx, .rcx, .rdi, .r11, .r12, .r13, .r14] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  obtain ⟨hrp, sepPF, sepPN, rP⟩ := out
  intro y0 b1 y1 b2 y2 b3 y3 b4
  xtail_block [Rind.X86_64.Mulx4x.sub, hrbx, hrcx, hrdi, hrax, hcf, hN, hT]

def subTailTrace (fp : Addr) : List Leak := [.addr (wa fp 5)]

set_option maxHeartbeats 4000000 in
theorem subTail_ok (s : S) (k : Nat) (ap bp np fp rp sp0 : Addr) (c b : Bool) (ar : Arr s k ap bp np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hr15 : s.vg.gpr .r15 = (BitVec.ofBool c).setWidth 64) (hcf : s.vg.cf = some b)
    (hrdi : s.vg.gpr .rdi = wa rp k) (hrdx : s.vg.gpr .rdx = BitVec.ofNat 64 (8 * k))
    (h5 : s.vg.mem.readW (wa fp 5) 64 = sp0) :
    let mk := (BitVec.ofBool c).setWidth 64 - 0 - (BitVec.ofBool b).setWidth 64
    ∃ s', execBlock I Rind.X86_64.Mulx4x.subTail s = some (s', subTailTrace fp) ∧
      s'.vg.gpr .r15 = mk ∧ s'.vg.gpr .rbx = wa fp 8 ∧ s'.vg.gpr .rdi = rp ∧ s'.vg.gpr .rsi = sp0 ∧
      s'.vg.xmm .xmm1 = shufDwords ((0 : BitVec 64) ++ mk) 0 ∧
      s'.vg.xmm .xmm0 = XBinOp.eval .pxor (s.vg.xmm .xmm0) (s.vg.xmm .xmm0) ∧
      s'.vg.mem = s.vg.mem ∧ FrameX s s' [.rbx, .rdi, .rsi, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  intro mk
  apply ex_of_eq
  · rw [execBlock_acc]
    xtail_run [Rind.X86_64.Mulx4x.subTail, hrsp, hr15, hcf, hrdi, hrdx, h5, wa_sub8]
    rfl
  · rfl
  · repeat' apply And.intro
    all_goals try refine FrameX.mk (fun r hr => ?_) ?_ ?_ rfl
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
      others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
      mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
      others_setMem, gpr_setXmm, mem_setXmm, wr_setXmm, xmm_setXmm, others_setXmm, reduceCtorEq, ↓reduceIte, *]
    all_goals first
      | with_reducible rfl
      | decide
      | skip

def copyTrace (fp rp : Addr) (j : Nat) : List Leak :=
  [.addr (wa fp (j + 8)), .addr (wa fp (j + 10)), .addr (wa rp j), .addr (wa rp (j + 2)), .addr (wa fp (j + 8)),
   .addr (wa fp (j + 10)), .addr (wa rp j), .addr (wa rp (j + 2))]

set_option maxHeartbeats 8000000 in
theorem copy_ok (s : S) (j k c : Nat) (ap bp np fp rp : Addr)
    (hjk : j + 4 ≤ k) (ar : Arr s k ap bp np fp) (out : OutX s k np fp rp)
    (al0 : (wa fp (j + 8)).toNat % 16 = 0) (al1 : (wa fp (j + 10)).toNat % 16 = 0)
    (hrbx : s.vg.gpr .rbx = wa fp (j + 8)) (hrdi : s.vg.gpr .rdi = wa rp j)
    (hrdx : s.vg.gpr .rdx = BitVec.ofNat 64 c) :
    let M := s.vg.mem
    let x0 := s.vg.xmm .xmm0
    let x1 := s.vg.xmm .xmm1
    let z := XBinOp.eval .pcmpeqd x0 x1
    let y0 := XBinOp.eval .por (XBinOp.eval .pand (M.readW (wa rp j) 128) z)
      (XBinOp.eval .pand (M.readW (wa fp (j + 8)) 128) x1)
    let y1 := XBinOp.eval .por (XBinOp.eval .pand (M.readW (wa rp (j + 2)) 128) z)
      (XBinOp.eval .pand (M.readW (wa fp (j + 10)) 128) x1)
    ∃ s', execBlock I Rind.X86_64.Mulx4x.copy s = some (s', copyTrace fp rp j) ∧
      s'.vg.xmm .xmm0 = XBinOp.eval .pxor z z ∧ s'.vg.xmm .xmm1 = x1 ∧
      s'.vg.gpr .rbx = wa fp (j + 12) ∧ s'.vg.gpr .rdi = wa rp (j + 4) ∧
      s'.vg.gpr .rdx = BitVec.ofNat 64 c - 32#64 ∧ s'.vg.zf = some (BitVec.ofNat 64 c - 32#64 == 0) ∧
      s'.vg.mem = (((M.writeW (wa fp (j + 8)) x0).writeW (wa fp (j + 10)) x0).writeW (wa rp j) y0).writeW
        (wa rp (j + 2)) y1 ∧
      FrameX s s' [.rbx, .rdi, .rdx] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  obtain ⟨hrp, sepPF, sepPN, rP⟩ := out
  intro M x0 x1 z y0 y1
  apply ex_of_eq
  · rw [execBlock_acc]
    xtail_run [Rind.X86_64.Mulx4x.copy, hrbx, hrdi, hrdx, al0, al1, signExtend_32]
    rfl
  · rfl
  · repeat' apply And.intro
    all_goals try refine FrameX.mk (fun r hr => ?_) ?_ ?_ rfl
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
      others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
      mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
      others_setMem, gpr_setXmm, mem_setXmm, wr_setXmm, xmm_setXmm, others_setXmm, zf_arithFlags, zf_setReg,
      zf_setFlags, zf_setXmm, zf_setMem, reduceCtorEq, ↓reduceIte, *]
    all_goals first
      | with_reducible rfl
      | skip

def epilogueTrace (fp sp0 : Addr) (k : Nat) : List Leak :=
  [.addr (wa fp (k + 8)), .addr (sp0 - 48#64), .addr (sp0 - 40#64), .addr (sp0 - 32#64), .addr (sp0 - 24#64),
   .addr (sp0 - 16#64), .addr (sp0 - 8#64)]

set_option hygiene false in
/-- Reads and the store in the claimed stack. -/
macro "xepi_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_setMem, wr_setMem]) <;>
     first
      | (refine inR (List.mem_append_right _ rS) ?_; simp only; bv_omega)
      | (refine inR rS ?_; simp only; bv_omega)
      | (unfold Apart; constructor <;> bv_omega)
      | omega)

set_option maxHeartbeats 4000000 in
theorem epilogue_ok (s : S) (k n : Nat) (fp sp0 v15 v14 v13 v12 vbp vbx : Addr) (rest : List Region)
    (hfp : fp.toNat + 8 * (k + 9) + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = fp) (hrbx : s.vg.gpr .rbx = wa fp (k + 8)) (hrdx : s.vg.gpr .rdx = 0)
    (hrsi : s.vg.gpr .rsi = sp0)
    (hwr : s.vg.wr = ⟨fp, n⟩ :: rest) (hn : n = sp0.toNat + 8 - fp.toNat)
    (h15 : s.vg.mem.readW (sp0 - 48#64) 64 = v15)
    (h14 : s.vg.mem.readW (sp0 - 40#64) 64 = v14) (h13 : s.vg.mem.readW (sp0 - 32#64) 64 = v13)
    (h12 : s.vg.mem.readW (sp0 - 24#64) 64 = v12) (hbp : s.vg.mem.readW (sp0 - 16#64) 64 = vbp)
    (hbx : s.vg.mem.readW (sp0 - 8#64) 64 = vbx) :
    ∃ s', execBlock I Rind.X86_64.Mulx4x.epilogue s = some (s', epilogueTrace fp sp0 k) ∧
      s'.vg.gpr .rsp = sp0 ∧ s'.vg.gpr .rax = 1 ∧ s'.vg.gpr .r15 = v15 ∧ s'.vg.gpr .r14 = v14 ∧
      s'.vg.gpr .r13 = v13 ∧ s'.vg.gpr .r12 = v12 ∧ s'.vg.gpr .rbp = vbp ∧ s'.vg.gpr .rbx = vbx ∧
      s'.vg.wr = ⟨sp0, 8⟩ :: rest ∧ s'.vg.rd = s.vg.rd ∧ s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo ∧
      s'.vg.mem = lose (s.vg.mem.writeW (wa fp (k + 8)) (0 : BitVec 64)) fp (sp0.toNat - fp.toNat) s.vg.unknowns := by
  have rS : (⟨fp, n⟩ : Region) ∈ s.vg.wr := by rw [hwr]; exact List.mem_cons_self
  apply ex_of_eq
  · rw [execBlock_acc]
    simp (config := { maxSteps := 4000000 }) (disch := xepi_disch) only [Rind.X86_64.Mulx4x.epilogue, hrsp, hrbx,
      hrdx, hrsi, execAcc_cons, execAcc_nil, load64_of, store64_of, Rind.X86_64.exec, Rind.X86_64.addrs,
      VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, readSrc, Option.map_some, Option.bind_some, State.ea,
      Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat,
      Int.reducePow, ea_pos, ea_comb, ofNat_add_pos, disp_neg, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv,
      Nat.reducePow, ofNat_zero, add_zero', signExtend_one, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      gpr_setMem, mem_setMem, rd_setMem, wr_setMem, readW_writeW_sep, reduceCtorEq, ↓reduceIte, List.map_nil,
      List.map_cons, List.append_nil, List.nil_append, List.cons_append, h15, h14, h13, h12, hbp, hbx]
    rw [moveSp_up _ _ n rest (by simp only [wr_setReg, wr_setMem, gpr_setReg, gpr_setMem, reduceCtorEq, ↓reduceIte, hrsp, hwr])
      (by simp only [gpr_setReg, gpr_setMem, reduceCtorEq, ↓reduceIte, hrsp]; omega)
      (by simp only [gpr_setReg, gpr_setMem, reduceCtorEq, ↓reduceIte, hrsp]; omega)]
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setMem, reduceCtorEq, ↓reduceIte, hrsp, hn]
    repeat' apply And.intro
    all_goals first | trivial | rfl | (congr 2; omega)

end rind.x86_64.mulx4x
