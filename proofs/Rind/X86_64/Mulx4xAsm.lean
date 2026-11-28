import RindIsa.X86_64.Mulx4x
import Rind.X86_64.Mulx4xModel
import Rind.X86_64.Mul4xTailAsm

/-! # bn_mulx4x_mont's blocks, run

Each block of the passes run symbolically: the words it stores, the registers and flags it leaves, as
`Mulx4xModel`'s functions of the words it reads. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mulx4x

section
variable (s : VG.X86_64.State)
@[simp] theorem of_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).of = s.of := rfl
@[simp] theorem of_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).of = b := rfl
@[simp] theorem of_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).of = some o := rfl
@[simp] theorem of_setMem (m : Mem) : (setMem s m).of = s.of := rfl
end

theorem ofInt_mul_toInt (x y : BitVec 64) : BitVec.ofInt 64 (x.toInt * y.toInt) = x * y := by
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem setWidth_zero32 : (0#32).setWidth 64 = 0 := by decide

/-- An index `n + a` past a constant `a`, moved on `b` words, as `simp` folds it. -/
theorem ofNat_add_add (n a b : Nat) (_h : b < 2 ^ 63) :
    BitVec.ofNat 64 (n + a) + BitVec.ofNat 64 b = BitVec.ofNat 64 (n + (a + b)) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]

/-- The arrays a block reaches: `k` words of `a`, `b`, and `n`, which it may read, and the frame's `k + 9`
words at `fp`, its seven slots, a gap, and `t`'s `k + 1` words, which it may write; the frame overlaps none of
the others, and none wraps. -/
structure Arr (s : S) (k : Nat) (ap bp np fp : Addr) : Prop where
  k29 : k < 2 ^ 29
  hap : ap.toNat + 8 * k ≤ 2 ^ 64
  hbp : bp.toNat + 8 * k ≤ 2 ^ 64
  hnp : np.toNat + 8 * k ≤ 2 ^ 64
  hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64
  sepA : ap.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ ap.toNat
  sepB : bp.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ bp.toNat
  sepN : np.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ np.toNat
  rA : ⟨ap, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rB : ⟨bp, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rN : ⟨np, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rF : ∃ L, 8 * (k + 9) ≤ L ∧ ⟨fp, L⟩ ∈ s.vg.wr

set_option hygiene false in
/-- Discharges the side conditions of a block's run. -/
macro "mulx_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem,
        wr_setMem]) <;>
     first
      | (refine inR (List.mem_append_right _ rF) ?_; simp only; bv_omega)
      | (refine inR rF ?_; simp only; bv_omega)
      | (refine inR rA ?_; simp only; bv_omega)
      | (refine inR rB ?_; simp only; bv_omega)
      | (refine inR rN ?_; simp only; bv_omega)
      | (unfold Apart; constructor <;> bv_omega)
      | omega)

/-- The lemmas that run a block of this routine. -/
syntax "mulx_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mulx_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := mulx_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, store64_of, ↓exec_dec, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, execAlu32, execMulx, execAdcx, execAdox, readSrc, readSrc32, Option.map_some,
      Option.bind_some, State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod,
      Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb, ofNat_add_add, ofNat_sub_ofNat,
      BitVec.xor_self, BitVec.zero_add, BitVec.sub_self, BitVec.add_sub_cancel, BitVec.reduceSub, ↓ofInt_mul_toInt,
      VG.X86_64.State.setReg32, setWidth_zero32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow,
      Nat.add_zero, ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero',
      readW_writeW_eq, readW_writeW_sep, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, of_setReg,
      gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, cf_arithFlags, of_arithFlags, gpr_setFlags,
      mem_setFlags, rd_setFlags, wr_setFlags, cf_setFlags, of_setFlags, gpr_setMem, mem_setMem, rd_setMem, wr_setMem,
      cf_setMem, of_setMem, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append,
      List.cons_append])

/-- Proves a block's lemma: runs it, matches the trace, and reads the registers, flags, and memory it leaves. -/
syntax "mulx_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mulx_block [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      mulx_run [$xs,*]
      rfl
    · rfl
    · repeat' apply And.intro
      all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
        others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
        mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
        others_setMem, cf_arithFlags, cf_setReg, cf_setFlags, cf_setMem, of_setReg, of_setFlags, of_arithFlags,
        of_setMem, zf_setReg, zf_setFlags, zf_arithFlags, zf_setMem, reduceCtorEq, ↓reduceIte, *]
      all_goals first
        | rfl
        | skip))

/-! ## The first pass's loop -/

def firstTrace (ap np fp : Addr) (j : Nat) : List Leak :=
  [.addr (wa ap (j + 1)), .addr (wa ap (j + 2)), .addr (wa ap (j + 3)), .addr (wa ap (j + 4)),
   .addr (wa np (j + 1)), .addr (wa np (j + 2)), .addr (wa np (j + 3)), .addr (wa fp (j + 8)),
   .addr (wa fp (j + 9)), .addr (wa np (j + 4)), .addr (wa fp (j + 10)), .addr (wa fp (j + 11))]

set_option maxHeartbeats 8000000 in
theorem first_ok (s : S) (j k c : Nat) (ap bp np fp b q cA cN : BitVec 64) (cf : Bool) (a n : Nat → BitVec 64)
    (hjk : j + 5 ≤ k) (ar : Arr s k ap bp np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (j + 1)) (hrcx : s.vg.gpr .rcx = wa np (j + 1))
    (hrbx : s.vg.gpr .rbx = wa fp (j + 9)) (hr9 : s.vg.gpr .r9 = b) (hrdx : s.vg.gpr .rdx = b)
    (hr8 : s.vg.gpr .r8 = q) (hrbp : s.vg.gpr .rbp = 0) (hr14 : s.vg.gpr .r14 = cA) (hr15 : s.vg.gpr .r15 = cN)
    (hrdi : s.vg.gpr .rdi = BitVec.ofNat 64 c) (hcf : s.vg.cf = some cf) (hof : s.vg.of = some false)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i) :
    let F := firstF (a (j + 1)) (a (j + 2)) (a (j + 3)) (a (j + 4)) (n (j + 1)) (n (j + 2)) (n (j + 3))
      (n (j + 4)) b q cA cN cf
    ∃ s', execBlock I Rind.X86_64.Mulx4x.first s = some (s', firstTrace ap np fp j) ∧
      s'.vg.gpr .rsi = wa ap (j + 5) ∧ s'.vg.gpr .rcx = wa np (j + 5) ∧ s'.vg.gpr .rbx = wa fp (j + 13) ∧
      s'.vg.gpr .rdx = b ∧ s'.vg.gpr .r14 = F.cA ∧ s'.vg.gpr .r15 = F.cN ∧ s'.vg.cf = some F.cf ∧
      s'.vg.gpr .rdi = BitVec.ofNat 64 c - 1 ∧ s'.vg.zf = some (BitVec.ofNat 64 c - 1 == 0) ∧
      s'.vg.of = some (subOverflow (BitVec.ofNat 64 c) 1 (BitVec.ofNat 64 c - 1)) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa fp (j + 8)) F.w0).writeW (wa fp (j + 9)) F.w1).writeW
        (wa fp (j + 10)) F.w2).writeW (wa fp (j + 11)) F.w3 ∧
      Frame s s' [.rax, .rdx, .rdi, .rsi, .rcx, .rbx, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  intro F
  mulx_block [Rind.X86_64.Mulx4x.first, hrsi, hrcx, hrbx, hr9, hr8, hrdx, hrbp, hr14, hr15, hrdi, hcf, hof, hA, hN]

def innerTrace (ap np fp : Addr) (j : Nat) : List Leak :=
  [.addr (wa ap (j + 1)), .addr (wa ap (j + 2)), .addr (wa fp (j + 9)), .addr (wa ap (j + 3)),
   .addr (wa fp (j + 10)), .addr (wa ap (j + 4)), .addr (wa fp (j + 11)), .addr (wa fp (j + 12)),
   .addr (wa np (j + 1)), .addr (wa np (j + 2)), .addr (wa np (j + 3)), .addr (wa fp (j + 8)),
   .addr (wa np (j + 4)), .addr (wa fp (j + 9)), .addr (wa fp (j + 10)), .addr (wa fp (j + 11))]

set_option maxHeartbeats 8000000 in
theorem inner_ok (s : S) (j k c : Nat) (ap bp np fp b q cA cN : BitVec 64) (cf : Bool) (a n T : Nat → BitVec 64)
    (hjk : j + 5 ≤ k) (ar : Arr s k ap bp np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (j + 1)) (hrcx : s.vg.gpr .rcx = wa np (j + 1))
    (hrbx : s.vg.gpr .rbx = wa fp (j + 9)) (hr9 : s.vg.gpr .r9 = b) (hrdx : s.vg.gpr .rdx = b)
    (hr8 : s.vg.gpr .r8 = q) (hrbp : s.vg.gpr .rbp = 0) (hr14 : s.vg.gpr .r14 = cA) (hr15 : s.vg.gpr .r15 = cN)
    (hrdi : s.vg.gpr .rdi = BitVec.ofNat 64 c) (hcf : s.vg.cf = some cf) (hof : s.vg.of = some false)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i, j + 9 ≤ i → i ≤ j + 12 → s.vg.mem.readW (wa fp i) 64 = T i) :
    let F := innerF (a (j + 1)) (a (j + 2)) (a (j + 3)) (a (j + 4)) (n (j + 1)) (n (j + 2)) (n (j + 3))
      (n (j + 4)) (T (j + 9)) (T (j + 10)) (T (j + 11)) (T (j + 12)) b q cA cN cf
    ∃ s', execBlock I Rind.X86_64.Mulx4x.inner s = some (s', innerTrace ap np fp j) ∧
      s'.vg.gpr .rsi = wa ap (j + 5) ∧ s'.vg.gpr .rcx = wa np (j + 5) ∧ s'.vg.gpr .rbx = wa fp (j + 13) ∧
      s'.vg.gpr .rdx = b ∧ s'.vg.gpr .r14 = F.cA ∧ s'.vg.gpr .r15 = F.cN ∧ s'.vg.cf = some F.cf ∧
      s'.vg.gpr .rdi = BitVec.ofNat 64 c - 1 ∧ s'.vg.zf = some (BitVec.ofNat 64 c - 1 == 0) ∧
      s'.vg.of = some (subOverflow (BitVec.ofNat 64 c) 1 (BitVec.ofNat 64 c - 1)) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa fp (j + 8)) F.w0).writeW (wa fp (j + 9)) F.w1).writeW
        (wa fp (j + 10)) F.w2).writeW (wa fp (j + 11)) F.w3 ∧
      Frame s s' [.rax, .rdx, .rdi, .rsi, .rcx, .rbx, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  intro F
  mulx_block [Rind.X86_64.Mulx4x.inner, hrsi, hrcx, hrbx, hr9, hr8, hrdx, hrbp, hr14, hr15, hrdi, hcf, hof, hA, hN,
    hT]

/-! ## The passes' first blocks -/

def body0Trace (ap bp np fp : Addr) : List Leak :=
  [.addr bp, .addr ap, .addr (wa ap 1), .addr (wa fp 1), .addr (wa ap 2), .addr (wa fp 3), .addr (wa ap 3),
   .addr np, .addr (wa np 1), .addr (wa np 2), .addr (wa fp 6), .addr (wa fp 8), .addr (wa np 3),
   .addr (wa fp 9), .addr (wa fp 10)]

/-- Every general register but the stack pointer. -/
abbrev allButSp : List Reg :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

set_option maxHeartbeats 8000000 in
theorem body0_ok (s : S) (k c : Nat) (ap bp np fp n0' : BitVec 64) (a bw n : Nat → BitVec 64)
    (hk : 8 ≤ k) (ar : Arr s k ap bp np fp)
    (hrsi : s.vg.gpr .rsi = ap) (hrdx : s.vg.gpr .rdx = bp) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hA0 : s.vg.mem.readW ap 64 = a 0) (hN0 : s.vg.mem.readW np 64 = n 0) (hB0 : s.vg.mem.readW bp 64 = bw 0)
    (h3 : s.vg.mem.readW (wa fp 3) 64 = n0') (h6 : s.vg.mem.readW (wa fp 6) 64 = BitVec.ofNat 64 c) :
    let q := mulLo (bw 0) (a 0) * n0'
    let F := body0F (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (bw 0) q
    ∃ s', execBlock I Rind.X86_64.Mulx4x.body0 s = some (s', body0Trace ap bp np fp) ∧
      s'.vg.gpr .rsi = wa ap 4 ∧ s'.vg.gpr .rcx = wa np 4 ∧ s'.vg.gpr .rbx = wa fp 12 ∧
      s'.vg.gpr .rdx = bw 0 ∧ s'.vg.gpr .r9 = bw 0 ∧ s'.vg.gpr .r8 = q ∧ s'.vg.gpr .rbp = 0 ∧
      s'.vg.gpr .rdi = BitVec.ofNat 64 c ∧ s'.vg.gpr .r14 = F.cA ∧ s'.vg.gpr .r15 = F.cN ∧
      s'.vg.cf = some F.cf ∧ s'.vg.of = some F.of ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa fp 1) (wa bp 1)).writeW (wa fp 8) F.w1).writeW (wa fp 9) F.w2).writeW
        (wa fp 10) F.w3 ∧
      Frame s s' allButSp := by
  obtain ⟨hk', hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  intro q F
  mulx_block [Rind.X86_64.Mulx4x.body0, hrsi, hrdx, hrcx, hrsp, hA, hN, hA0, hN0, hB0, h3, h6]

def outerHeadTrace (ap bp np fp : Addr) (k i : Nat) : List Leak :=
  [.addr (wa bp i), .addr (wa fp (k + 8)), .addr ap, .addr (wa ap 1), .addr (wa fp 8), .addr (wa ap 2),
   .addr (wa fp 9), .addr (wa fp 10), .addr (wa fp 1), .addr (wa fp 3), .addr (wa ap 3), .addr (wa fp 11),
   .addr np, .addr (wa np 1), .addr (wa np 2), .addr (wa fp 8), .addr (wa np 3), .addr (wa fp 9),
   .addr (wa fp 6), .addr (wa fp 10)]

set_option maxHeartbeats 8000000 in
theorem outerHead_ok (s : S) (k i c : Nat) (ap bp np fp n0' V : BitVec 64) (a bw n T : Nat → BitVec 64)
    (hk : 8 ≤ k) (hi : i < k) (ar : Arr s k ap bp np fp)
    (hrdi : s.vg.gpr .rdi = wa bp i) (hrsi : s.vg.gpr .rsi = wa ap k) (hrcx : s.vg.gpr .rcx = wa np k)
    (hrax : s.vg.gpr .rax = BitVec.ofNat 64 k * 8#64) (hrbx : s.vg.gpr .rbx = wa fp (k + 8))
    (hr15 : s.vg.gpr .r15 = V) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s.vg.mem.readW (wa bp i) 64 = bw i)
    (hA0 : s.vg.mem.readW ap 64 = a 0) (hN0 : s.vg.mem.readW np 64 = n 0)
    (hT : ∀ i, 8 ≤ i → i ≤ 11 → s.vg.mem.readW (wa fp i) 64 = T i)
    (h3 : s.vg.mem.readW (wa fp 3) 64 = n0') (h6 : s.vg.mem.readW (wa fp 6) 64 = BitVec.ofNat 64 c) :
    let q := outerHeadX (a 0) (T 8) (bw i) * n0'
    let F := outerHeadF (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (T 8) (T 9) (T 10) (T 11) (bw i) q
    ∃ s', execBlock I Rind.X86_64.Mulx4x.outerHead s = some (s', outerHeadTrace ap bp np fp k i) ∧
      s'.vg.gpr .rsi = wa ap 4 ∧ s'.vg.gpr .rcx = wa np 4 ∧ s'.vg.gpr .rbx = wa fp 12 ∧
      s'.vg.gpr .rdx = bw i ∧ s'.vg.gpr .r9 = bw i ∧ s'.vg.gpr .r8 = q ∧ s'.vg.gpr .rbp = 0 ∧
      s'.vg.gpr .rdi = BitVec.ofNat 64 c ∧ s'.vg.gpr .r14 = F.cA ∧ s'.vg.gpr .r15 = F.cN ∧
      s'.vg.cf = some F.cf ∧ s'.vg.of = some F.of ∧
      s'.vg.mem = ((((s.vg.mem.writeW (wa fp (k + 8)) V).writeW (wa fp 1) (wa bp (i + 1))).writeW (wa fp 8) F.w1).writeW
        (wa fp 9) F.w2).writeW (wa fp 10) F.w3 ∧
      Frame s s' allButSp := by
  obtain ⟨hk', hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  intro q F
  mulx_block [Rind.X86_64.Mulx4x.outerHead, hrdi, hrsi, hrcx, hrax, hrbx, hr15, hrsp, hA, hN, hB, hA0, hN0, hT, h3,
    h6, ofNat_add_pos]

/-! ## The passes' top words -/

def firstTailTrace (fp : Addr) (k : Nat) : List Leak := [.addr fp, .addr (wa fp 1), .addr (wa fp (k + 7))]

set_option maxHeartbeats 8000000 in
theorem firstTail_ok (s : S) (k : Nat) (ap bp np fp cA cN X0 X1 : BitVec 64) (cf : Bool)
    (hk : 8 ≤ k) (ar : Arr s k ap bp np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrbx : s.vg.gpr .rbx = wa fp (k + 8)) (hrbp : s.vg.gpr .rbp = 0)
    (hr14 : s.vg.gpr .r14 = cA) (hr15 : s.vg.gpr .r15 = cN) (hcf : s.vg.cf = some cf)
    (h0 : s.vg.mem.readW fp 64 = X0) (h1 : s.vg.mem.readW (wa fp 1) 64 = X1) :
    ∃ s', execBlock I Rind.X86_64.Mulx4x.firstTail s = some (s', firstTailTrace fp k) ∧
      s'.vg.gpr .rax = X0 ∧ s'.vg.gpr .rdi = X1 ∧ s'.vg.gpr .r14 = (topF cA cN cf).1 ∧
      s'.vg.gpr .r15 = 0 - (BitVec.ofBool (topF cA cN cf).2).setWidth 64 ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp (k + 7)) (topF cA cN cf).1 ∧
      Frame s s' [.rax, .rdi, .r14, .r15] := by
  obtain ⟨hk', hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  mulx_block [Rind.X86_64.Mulx4x.firstTail, hrsp, hrbx, hrbp, hr14, hr15, hcf, h0, h1]

def outerTailTrace (fp : Addr) (k : Nat) : List Leak :=
  [.addr fp, .addr (wa fp 1), .addr (wa fp (k + 8)), .addr (wa fp (k + 7)), .addr (wa fp 2)]

set_option maxHeartbeats 8000000 in
theorem outerTail_ok (s : S) (k : Nat) (ap bp np fp cA cN T X0 X1 X2 : BitVec 64) (cf : Bool)
    (hk : 8 ≤ k) (ar : Arr s k ap bp np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrbx : s.vg.gpr .rbx = wa fp (k + 8)) (hrbp : s.vg.gpr .rbp = 0)
    (hr14 : s.vg.gpr .r14 = cA) (hr15 : s.vg.gpr .r15 = cN) (hcf : s.vg.cf = some cf)
    (h0 : s.vg.mem.readW fp 64 = X0) (h1 : s.vg.mem.readW (wa fp 1) 64 = X1)
    (h2 : s.vg.mem.readW (wa fp 2) 64 = X2) (hT : s.vg.mem.readW (wa fp (k + 8)) 64 = T) :
    ∃ s', execBlock I Rind.X86_64.Mulx4x.outerTail s = some (s', outerTailTrace fp k) ∧
      s'.vg.gpr .rax = X0 ∧ s'.vg.gpr .rdi = X1 ∧ s'.vg.gpr .r14 = (topT cA cN T cf).1 ∧
      s'.vg.gpr .r15 = 0 - (BitVec.ofBool (topT cA cN T cf).2).setWidth 64 ∧ s'.vg.zf = some (X1 - X2 == 0) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp (k + 7)) (topT cA cN T cf).1 ∧
      Frame s s' [.rax, .rdi, .rbp, .r14, .r15] := by
  obtain ⟨hk', hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  mulx_block [Rind.X86_64.Mulx4x.outerTail, hrsp, hrbx, hrbp, hr14, hr15, hcf, h0, h1, h2, hT]

end rind.x86_64.mulx4x
