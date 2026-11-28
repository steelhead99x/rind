import Rind.X86_64.Mul4xAsm

/-! # bn_mul4x_mont's last blocks

`final`, which starts subtracting `n` from `t`, the four words of the subtraction `sub`, and `subTail`,
which ends it and makes the masks. -/

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mul4x

theorem ofNat_shr (x n : Nat) (h : x < 2 ^ 64) : BitVec.ofNat 64 x >>> n = BitVec.ofNat 64 (x / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) h)]

set_option hygiene false in
/-- `mul4x_disch`, and `rp`'s region `rP`. -/
macro "tail_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_execMul, wr_execMul, rd_execImul, wr_execImul, rd_arithFlags,
        wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem, wr_setMem]) <;>
     first
      | (refine inR (List.mem_append_right _ rT) ?_; simp only; bv_omega)
      | (refine inR (List.mem_append_right _ rP) ?_; simp only; bv_omega)
      | (refine inR rT ?_; simp only; bv_omega)
      | (refine inR rP ?_; simp only; bv_omega)
      | (refine inR rN ?_; simp only; bv_omega)
      | (unfold Apart; constructor <;> bv_omega)
      | omega)

/-- `mul4x_run` with `tail_disch`. -/
syntax "tail_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| tail_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := tail_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, store64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, readSrc, Option.map_some, Option.bind_some, decide_carry,
      State.ea, m, mx, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb,
      ofNat_add_pos, ofNat_sub_ofNat, BitVec.xor_self, BitVec.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.add_zero,
      ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero', decide_carry', readW_writeW_eq, readW_writeW_sep,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, gpr_arithFlags, mem_arithFlags, rd_arithFlags,
      wr_arithFlags, cf_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, gpr_setMem, mem_setMem,
      rd_setMem, wr_setMem, cf_setMem, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append,
      List.cons_append])

/-- `mul4x_block` with `tail_run`. -/
syntax "tail_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| tail_block [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      tail_run [$xs,*]
      rfl
    · rfl
    · repeat' apply And.intro
      all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
        others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
        mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
        others_setMem, cf_arithFlags, zf_arithFlags, zf_setReg, cf_setReg, reduceCtorEq, ↓reduceIte, *]
      all_goals first
        | rfl
        | (simp only [Option.some.injEq, decide_eq_decide, BitVec.toNat_ofNat]; omega)
        | skip))

def finalTrace (np tp : Addr) (k : Nat) : List Leak :=
  [.addr (wa tp (k + 2)), .addr tp, .addr (wa tp 1), .addr np, .addr (wa tp 2), .addr (wa tp 3), .addr (wa np 1)]

set_option maxHeartbeats 4000000 in
theorem final_ok (s : S) (k : Nat) (ap bp np n0p tp rp : BitVec 64) (t n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (ar : Arrays s k ap bp np n0p tp)
    (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i) (hN0 : s.vg.mem.readW np 64 = n 0)
    (hT : ∀ i ≤ k, s.vg.mem.readW (wa tp i) 64 = t i) (hT0 : s.vg.mem.readW tp 64 = t 0)
    (hrp : s.vg.mem.readW (wa tp (k + 2)) 64 = rp) :
    ∃ s', execBlock I final s = some (s', finalTrace np tp k) ∧
      s'.vg.gpr .rdi = rp ∧ s'.vg.gpr .r15 = BitVec.ofNat 64 ((k - 4) / 4) ∧ s'.vg.gpr .rsi = tp ∧
      s'.vg.gpr .r14 = 0 ∧ s'.vg.gpr .rax = t 0 - n 0 ∧
      s'.vg.gpr .rdx = t 1 - n 1 - (BitVec.ofBool (decide ((t 0).toNat < (n 0).toNat))).setWidth 64 ∧
      s'.vg.cf = some (decide ((t 1).toNat < (n 1).toNat + (decide ((t 0).toNat < (n 0).toNat)).toNat)) ∧
      s'.vg.gpr .rbx = t 2 ∧ s'.vg.gpr .rbp = t 3 ∧ s'.vg.mem = s.vg.mem ∧
      Frame s s' [.rax, .rdx, .rdi, .rsi, .rbx, .rbp, .r14, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  tail_block [final, hrcx, hrsp, hr9, hN, hN0, hT, hT0, hrp, ofNat_add_neg, ofNat_shr, execShift, Nat.reduceLeDiff,
    and_self]

/-- Where `rp` lies: `k` words, which the routine may write, apart from `t` and `n`. -/
structure Out (s : S) (k : Nat) (np tp rp : Addr) : Prop where
  hrp : rp.toNat + 8 * k ≤ 2 ^ 64
  sepT : rp.toNat + 8 * k ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ rp.toNat
  sepN : rp.toNat + 8 * k ≤ np.toNat ∨ np.toNat + 8 * k ≤ rp.toNat
  rP : ⟨rp, 8 * k⟩ ∈ s.vg.wr

def subTrace (np tp rp : Addr) (j : Nat) : List Leak :=
  [.addr (wa rp j), .addr (wa rp (j + 1)), .addr (wa np (j + 2)), .addr (wa tp (j + 4)), .addr (wa tp (j + 5)),
   .addr (wa np (j + 3)), .addr (wa rp (j + 2)), .addr (wa rp (j + 3)), .addr (wa np (j + 4)), .addr (wa tp (j + 6)),
   .addr (wa tp (j + 7)), .addr (wa np (j + 5))]

set_option maxHeartbeats 8000000 in
theorem sub_ok (s : S) (j k c : Nat) (ap bp np n0p tp rp x0 x1 x2 x3 : BitVec 64) (b : Bool) (t n : Nat → BitVec 64)
    (hjk : j + 8 ≤ k) (ar : Arrays s k ap bp np n0p tp) (out : Out s k np tp rp)
    (hrdi : s.vg.gpr .rdi = rp) (hrsi : s.vg.gpr .rsi = tp) (hrcx : s.vg.gpr .rcx = np)
    (hr14 : s.vg.gpr .r14 = BitVec.ofNat 64 j) (hr15 : s.vg.gpr .r15 = BitVec.ofNat 64 c)
    (hrax : s.vg.gpr .rax = x0) (hrdx : s.vg.gpr .rdx = x1) (hrbx : s.vg.gpr .rbx = x2)
    (hrbp : s.vg.gpr .rbp = x3) (hcf : s.vg.cf = some b)
    (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i) (hT : ∀ i ≤ k, s.vg.mem.readW (wa tp i) 64 = t i) :
    let y2 := x2 - n (j + 2) - (BitVec.ofBool b).setWidth 64
    let b3 := decide (x2.toNat < (n (j + 2)).toNat + b.toNat)
    let y3 := x3 - n (j + 3) - (BitVec.ofBool b3).setWidth 64
    let b4 := decide (x3.toNat < (n (j + 3)).toNat + b3.toNat)
    let y4 := t (j + 4) - n (j + 4) - (BitVec.ofBool b4).setWidth 64
    let b5 := decide ((t (j + 4)).toNat < (n (j + 4)).toNat + b4.toNat)
    let y5 := t (j + 5) - n (j + 5) - (BitVec.ofBool b5).setWidth 64
    let b6 := decide ((t (j + 5)).toNat < (n (j + 5)).toNat + b5.toNat)
    ∃ s', execBlock I sub s = some (s', subTrace np tp rp j) ∧
      s'.vg.gpr .rax = y4 ∧ s'.vg.gpr .rdx = y5 ∧ s'.vg.gpr .rbx = t (j + 6) ∧ s'.vg.gpr .rbp = t (j + 7) ∧
      s'.vg.cf = some b6 ∧ s'.vg.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 c - 1 ∧ s'.vg.zf = some (BitVec.ofNat 64 c - 1 == 0) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa rp j) x0).writeW (wa rp (j + 1)) x1).writeW (wa rp (j + 2)) y2).writeW
        (wa rp (j + 3)) y3 ∧
      Frame s s' [.rax, .rdx, .rbx, .rbp, .r14, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  obtain ⟨hrp, sepPT, sepPN, rP⟩ := out
  intro y2 b3 y3 b4 y4 b5 y5 b6
  tail_block [sub, hrdi, hrsi, hrcx, hr14, hr15, hrax, hrdx, hrbx, hrbp, hcf, hN, hT]

section
variable (s : VG.X86_64.State) (d : XReg) (v : BitVec 128)
@[simp] theorem gpr_setXmm : (s.setXmm d v).gpr = s.gpr := rfl
@[simp] theorem mem_setXmm : (s.setXmm d v).mem = s.mem := rfl
@[simp] theorem rd_setXmm : (s.setXmm d v).rd = s.rd := rfl
@[simp] theorem wr_setXmm : (s.setXmm d v).wr = s.wr := rfl
@[simp] theorem cf_setXmm : (s.setXmm d v).cf = s.cf := rfl
@[simp] theorem zf_setXmm : (s.setXmm d v).zf = s.zf := rfl
@[simp] theorem others_setXmm : others (s.setXmm d v) = others s := rfl
@[simp] theorem xmm_setXmm (r : XReg) : (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl
end

/-- What a block leaves unchanged, but the vector registers too. -/
structure FrameX (s s' : S) (gs : List Reg) : Prop where
  gpr : ∀ r, r ∉ gs → s'.vg.gpr r = s.vg.gpr r
  others : others s'.vg = others s.vg
  wr : s'.vg.wr = s.vg.wr
  lo : s'.lo = s.lo

def subTailTrace (np tp rp : Addr) (j : Nat) : List Leak :=
  [.addr (wa rp j), .addr (wa tp (j + 4)), .addr (wa np (j + 2)), .addr (wa rp (j + 1)), .addr (wa np (j + 3)),
   .addr (wa rp (j + 2)), .addr (wa rp (j + 3))]

set_option maxHeartbeats 8000000 in
theorem subTail_ok (s : S) (j : Nat) (ap bp np n0p tp rp x0 x1 x2 x3 : BitVec 64) (b : Bool) (t n : Nat → BitVec 64)
    (ar : Arrays s (j + 4) ap bp np n0p tp) (out : Out s (j + 4) np tp rp)
    (hrdi : s.vg.gpr .rdi = rp) (hrsi : s.vg.gpr .rsi = tp) (hrcx : s.vg.gpr .rcx = np)
    (hr14 : s.vg.gpr .r14 = BitVec.ofNat 64 j) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (j + 4))
    (hrax : s.vg.gpr .rax = x0) (hrdx : s.vg.gpr .rdx = x1) (hrbx : s.vg.gpr .rbx = x2)
    (hrbp : s.vg.gpr .rbp = x3) (hcf : s.vg.cf = some b)
    (hN : ∀ i < j + 4, s.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i ≤ j + 4, s.vg.mem.readW (wa tp i) 64 = t i) :
    let y2 := x2 - n (j + 2) - (BitVec.ofBool b).setWidth 64
    let b3 := decide (x2.toNat < (n (j + 2)).toNat + b.toNat)
    let y3 := x3 - n (j + 3) - (BitVec.ofBool b3).setWidth 64
    let b4 := decide (x3.toNat < (n (j + 3)).toNat + b3.toNat)
    let mask := t (j + 4) - 0 - (BitVec.ofBool b4).setWidth 64
    let x4 := shufDwords ((0 : BitVec 64) ++ mask) 0
    ∃ s', execBlock I subTail s = some (s', subTailTrace np tp rp j) ∧
      s'.vg.xmm .xmm0 = XBinOp.eval .pxor (s.vg.xmm .xmm0) (s.vg.xmm .xmm0) ∧ s'.vg.xmm .xmm4 = x4 ∧
      s'.vg.xmm .xmm5 = XBinOp.eval .pxor (XBinOp.eval .pcmpeqd (s.vg.xmm .xmm5) (s.vg.xmm .xmm5)) x4 ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 ((j + 4) / 4) ∧ s'.vg.gpr .rax = 0 ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa rp j) x0).writeW (wa rp (j + 1)) x1).writeW (wa rp (j + 2)) y2).writeW
        (wa rp (j + 3)) y3 ∧
      FrameX s s' [.rax, .rdx, .rbx, .rbp, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  obtain ⟨hrp, sepPT, sepPN, rP⟩ := out
  intro y2 b3 y3 b4 mask x4
  apply ex_of_eq
  · rw [execBlock_acc]
    tail_run [subTail, hrdi, hrsi, hrcx, hr14, hr9, hrax, hrdx, hrbx, hrbp, hcf, hN, hT, XOp.exec, execAlu32,
      readSrc32, VG.X86_64.State.setReg32, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, cf_setXmm, xmm_setXmm,
      ofNat_shr, execShift, Nat.reduceLeDiff, and_self, signExtend_zero']
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

/-! ## The copy -/

section
variable (s : VG.X86_64.State)
theorem load128_of {a : Addr} (h : InRegions (s.rd ++ s.wr) a 16) : s.load128 a = some (s.mem.readW a 128) := by
  simp [State.load128, h]
theorem store128_of {a : Addr} {v : BitVec 128} (h : InRegions s.wr a 16) :
    s.store128 a v = some (setMem s (s.mem.writeW a v)) := by
  simp [State.store128, h, setMem]
end

/-- `dec`'s flags, folded. -/
theorem exec_dec (d : Reg) (s : S) : Rind.X86_64.exec (.dec d) s =
    some { s with vg := (s.vg.setFlags s.vg.cf (some (subOverflow (s.vg.gpr d) 1 (s.vg.gpr d - 1)))
      (some (s.vg.gpr d - 1 == 0)) (some (s.vg.gpr d - 1).msb)).setReg d (s.vg.gpr d - 1) } := rfl

theorem mul_ofNat_one (x : BitVec 64) : x * BitVec.ofNat 64 1 = x := BitVec.mul_one x

theorem mul8_add (x y : BitVec 64) : x * 8#64 + y * 8#64 = (x + y) * 8#64 := by rw [BitVec.add_mul]

set_option hygiene false in
/-- `tail_disch`, and 16-byte accesses apart. -/
macro "copy_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem,
        wr_setMem, rd_setXmm, wr_setXmm]) <;>
     first
      | (refine inR (List.mem_append_right _ rT) ?_; simp only; bv_omega)
      | (refine inR (List.mem_append_right _ rP) ?_; simp only; bv_omega)
      | (refine inR rT ?_; simp only; bv_omega)
      | (refine inR rP ?_; simp only; bv_omega)
      | (constructor <;> bv_omega)
      | omega)

def copyTrace (tp rp : Addr) (j : Nat) : List Leak :=
  [.addr (wa tp j), .addr (wa rp j), .addr (wa tp (j + 2)), .addr (wa tp j), .addr (wa rp (j + 2)),
   .addr (wa rp j), .addr (wa tp (j + 2)), .addr (wa rp (j + 2))]

set_option maxHeartbeats 8000000 in
theorem copy_ok (s : S) (j k c : Nat) (ap bp np n0p tp rp : BitVec 64)
    (hjk : j + 4 ≤ k) (ar : Arrays s k ap bp np n0p tp) (out : Out s k np tp rp)
    (al0 : (wa tp j).toNat % 16 = 0) (al1 : (wa tp (j + 2)).toNat % 16 = 0)
    (hrdi : s.vg.gpr .rdi = rp) (hrsp : s.vg.gpr .rsp = tp)
    (hrax : s.vg.gpr .rax = BitVec.ofNat 64 j * 8#64) (hr15 : s.vg.gpr .r15 = BitVec.ofNat 64 c) :
    let M := s.vg.mem
    let x0 := s.vg.xmm .xmm0
    let x4 := s.vg.xmm .xmm4
    let x5 := s.vg.xmm .xmm5
    let y0 := XBinOp.eval .por (XBinOp.eval .pand (M.readW (wa tp j) 128) x4) (XBinOp.eval .pand (M.readW (wa rp j) 128) x5)
    let y1 := XBinOp.eval .por (XBinOp.eval .pand (M.readW (wa tp (j + 2)) 128) x4)
      (XBinOp.eval .pand (M.readW (wa rp (j + 2)) 128) x5)
    ∃ s', execBlock I copy s = some (s', copyTrace tp rp j) ∧
      s'.vg.xmm .xmm0 = x0 ∧ s'.vg.xmm .xmm4 = x4 ∧ s'.vg.xmm .xmm5 = x5 ∧
      s'.vg.gpr .rax = BitVec.ofNat 64 (j + 4) * 8#64 ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 c - 1 ∧ s'.vg.zf = some (BitVec.ofNat 64 c - 1 == 0) ∧
      s'.vg.mem = (((M.writeW (wa tp j) x0).writeW (wa rp j) y0).writeW (wa tp (j + 2)) x0).writeW (wa rp (j + 2)) y1 ∧
      FrameX s s' [.rax, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  obtain ⟨hrp, sepPT, sepPN, rP⟩ := out
  intro M x0 x4 x5 y0 y1
  apply ex_of_eq
  · rw [execBlock_acc]
    simp (config := { maxSteps := 4000000 }) (disch := copy_disch) only [copy, hrdi, hrsp, hrax, hr15, al0, al1,
      execAcc_cons, execAcc_nil, load128_of, store128_of, ↓exec_dec, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs,
      VG.X86_64.exec, XOp.exec, Option.map_some, Option.bind_some, State.ea, m, mx, ofInt_lit, Int.reduceNeg,
      Int.reduceMod, Int.reduceToNat, Int.reducePow, mul_ofNat_one, ea_pos, disp_pos, ea_comb, mul8_add, ofNat_add_pos,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, Nat.add_zero, ofNat_zero, add_zero',
      readW_writeW_disj, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, gpr_setMem, mem_setMem, rd_setMem, wr_setMem, gpr_setXmm, mem_setXmm, rd_setXmm,
      wr_setXmm, xmm_setXmm, xmm_setMem, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil,
      List.nil_append, List.cons_append]
    rfl
  · rfl
  · repeat' apply And.intro
    all_goals try refine FrameX.mk (fun r hr => ?_) ?_ ?_ rfl
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
      others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
      mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
      others_setMem, gpr_setXmm, mem_setXmm, wr_setXmm, xmm_setXmm, others_setXmm, zf_arithFlags, zf_setReg,
      zf_setFlags, zf_setXmm, zf_setMem, reduceCtorEq,
      ↓reduceIte, *]
    all_goals first
      | with_reducible rfl
      | skip

/-! ## The epilogue -/

/-- `lea rsp` raising the stack pointer by at most what the function claimed. -/
theorem moveSp_up (s : S) (v : Addr) (n : Nat) (rest : List Region)
    (hwr : s.vg.wr = ⟨s.vg.gpr .rsp, n⟩ :: rest) (h1 : (s.vg.gpr .rsp).toNat < v.toNat)
    (h2 : v.toNat - (s.vg.gpr .rsp).toNat ≤ n) :
    Rind.X86_64.moveSp s v = some { s with vg := { s.vg.setReg .rsp v with
        wr := ⟨v, n - (v.toNat - (s.vg.gpr .rsp).toNat)⟩ :: rest,
        mem := lose s.vg.mem (s.vg.gpr .rsp) (v.toNat - (s.vg.gpr .rsp).toNat) s.vg.unknowns,
        unknowns := fun i => s.vg.unknowns (i + 2 * ((v.toNat - (s.vg.gpr .rsp).toNat + 7) / 8)) } } := by
  have hc : Rind.X86_64.claimed s.vg = some n := by simp [Rind.X86_64.claimed, hwr]
  simp only [Rind.X86_64.moveSp, hc, Option.bind_some, hwr, List.tail_cons]
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

theorem disp_neg (b : BitVec 64) (L : Nat) (h : 2 ^ 63 ≤ L ∧ L < 2 ^ 64) :
    b + BitVec.ofNat 64 L = b - BitVec.ofNat 64 (2 ^ 64 - L) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem signExtend_one : (1 : BitVec 32).signExtend 64 = 1 := by decide

def epilogueTrace (tp sp0 : Addr) (k : Nat) : List Leak :=
  [.addr (wa tp (k + 1)), .addr (sp0 - 48#64), .addr (sp0 - 40#64), .addr (sp0 - 32#64), .addr (sp0 - 24#64),
   .addr (sp0 - 16#64), .addr (sp0 - 8#64)]

set_option hygiene false in
/-- Reads in the claimed stack. -/
macro "epi_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg]) <;>
     first
      | (refine inR (List.mem_append_right _ rS) ?_; simp only; bv_omega)
      | omega)

set_option maxHeartbeats 4000000 in
theorem epilogue_ok (s : S) (k n : Nat) (tp sp0 v15 v14 v13 v12 vbp vbx : Addr) (rest : List Region)
    (hk : k < 2 ^ 32) (htp : tp.toNat + 8 * (k + 3) + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = tp) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hwr : s.vg.wr = ⟨tp, n⟩ :: rest) (hn : n = sp0.toNat + 8 - tp.toNat)
    (hS : s.vg.mem.readW (wa tp (k + 1)) 64 = sp0) (h15 : s.vg.mem.readW (sp0 - 48#64) 64 = v15)
    (h14 : s.vg.mem.readW (sp0 - 40#64) 64 = v14) (h13 : s.vg.mem.readW (sp0 - 32#64) 64 = v13)
    (h12 : s.vg.mem.readW (sp0 - 24#64) 64 = v12) (hbp : s.vg.mem.readW (sp0 - 16#64) 64 = vbp)
    (hbx : s.vg.mem.readW (sp0 - 8#64) 64 = vbx) :
    ∃ s', execBlock I epilogue s = some (s', epilogueTrace tp sp0 k) ∧
      s'.vg.gpr .rsp = sp0 ∧ s'.vg.gpr .rax = 1 ∧ s'.vg.gpr .r15 = v15 ∧ s'.vg.gpr .r14 = v14 ∧
      s'.vg.gpr .r13 = v13 ∧ s'.vg.gpr .r12 = v12 ∧ s'.vg.gpr .rbp = vbp ∧ s'.vg.gpr .rbx = vbx ∧
      s'.vg.wr = ⟨sp0, 8⟩ :: rest ∧ s'.vg.rd = s.vg.rd ∧ s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo ∧
      s'.vg.mem = lose s.vg.mem tp (sp0.toNat - tp.toNat) s.vg.unknowns := by
  have rS : (⟨tp, n⟩ : Region) ∈ s.vg.wr := by rw [hwr]; exact List.mem_cons_self
  apply ex_of_eq
  · rw [execBlock_acc]
    simp (config := { maxSteps := 4000000 }) (disch := epi_disch) only [epilogue, hrsp, hr9, hS, h15, h14, h13,
      h12, hbp, hbx, execAcc_cons, execAcc_nil, load64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs,
      srcAddrs, VG.X86_64.exec, readSrc, Option.map_some, Option.bind_some, State.ea, m, mx, ofInt_lit,
      Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow, ea_pos, ea_comb, ofNat_add_pos, disp_neg,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, ofNat_zero, add_zero', signExtend_one,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append]
    rw [moveSp_up _ _ n rest (by simp only [wr_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp, hwr])
      (by simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp]; omega)
      (by simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp]; omega)]
    rfl
  · rfl
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, hrsp, hn]
    repeat' apply And.intro
    all_goals first | trivial | rfl | (congr 2; omega)

end rind.x86_64.mul4x
