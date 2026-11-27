import RindIsa.X86_64.Mul4x
import Rind.X86_64.Mul4xModel

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mul4x

/-- What a block leaves unchanged: the general registers but `gs`, and the rest of the state but memory and
the flags. -/
structure Frame (s s' : S) (gs : List Reg) : Prop where
  gpr : ∀ r, r ∉ gs → s'.vg.gpr r = s.vg.gpr r
  others : others s'.vg = others s.vg
  wr : s'.vg.wr = s.vg.wr
  xmm : s'.vg.xmm = s.vg.xmm
  lo : s'.lo = s.lo

/-- The address of word `i` of the array at `p`. -/
abbrev wa (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 i * 8#64

def firstTrace (ap np tp : Addr) (j : Nat) : List Leak :=
  [.addr (wa np (j + 1)), .addr (wa ap (j + 2)), .addr (wa tp j),
   .addr (wa np (j + 2)), .addr (wa ap (j + 3)), .addr (wa tp (j + 1)),
   .addr (wa np (j + 3)), .addr (wa ap (j + 4)), .addr (wa tp (j + 2)),
   .addr (wa np (j + 4)), .addr (wa ap (j + 5)), .addr (wa tp (j + 3))]

set_option hygiene false in
/-- Discharges the side conditions of a block's run. -/
macro "mul4x_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_execMul, wr_execMul, rd_execImul, wr_execImul, rd_arithFlags,
        wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem, wr_setMem]) <;>
     first
      | (refine inR (List.mem_append_right _ rT) ?_; simp only; bv_omega)
      | (refine inR rT ?_; simp only; bv_omega)
      | (refine inR rA ?_; simp only; bv_omega)
      | (refine inR rN ?_; simp only; bv_omega)
      | (refine inR rB ?_; simp only; bv_omega)
      | (refine inR rN0 ?_; simp only; bv_omega)
      | (unfold Apart; constructor <;> bv_omega)
      | omega)

/-- The lemmas that run a block of this routine. -/
syntax "mul4x_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mul4x_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := mul4x_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, store64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, readSrc, Option.map_some, Option.bind_some, decide_carry,
      State.ea, m, mx, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb,
      ofNat_add_pos, ofNat_sub_ofNat, BitVec.xor_self, BitVec.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.add_zero,
      ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero', decide_carry', readW_writeW_eq, readW_writeW_sep,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, gpr_arithFlags, mem_arithFlags, rd_arithFlags,
      wr_arithFlags, cf_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, gpr_setMem, mem_setMem,
      rd_setMem, wr_setMem, cf_setMem, gpr_execMul, mem_execMul, rd_execMul, wr_execMul,
      gpr_execImul, mem_execImul, rd_execImul, wr_execImul, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append,
      List.cons_append])

/-- Proves a block's lemma: runs it, matches the trace, and reads the
registers, flags, and memory it leaves. -/
syntax "mul4x_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mul4x_block [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      mul4x_run [$xs,*]
      rfl
    · rfl
    · repeat' apply And.intro
      all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg, others_setReg, gpr_arithFlags,
        mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags, mem_setFlags, wr_setFlags,
        xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem, others_setMem, gpr_execMul,
        mem_execMul, wr_execMul, xmm_execMul, others_execMul, gpr_execImul, mem_execImul, wr_execImul, xmm_execImul,
        others_execImul, cf_arithFlags, reduceCtorEq, ↓reduceIte, *]
      all_goals first
        | rfl
        | (simp only [Option.some.injEq, decide_eq_decide, BitVec.toNat_ofNat]; omega)
        | skip))

/-- The arrays a block reaches, `k` words of `a` and `n` and `k + 3` of `t`, which the routine may read, and
write in `t`'s case; `t` overlaps neither of the others, and none wraps. -/
structure Arrays (s : S) (k : Nat) (ap bp np n0p tp : Addr) : Prop where
  k32 : k < 2 ^ 32
  hap : ap.toNat + 8 * k ≤ 2 ^ 64
  hbp : bp.toNat + 8 * k ≤ 2 ^ 64
  hnp : np.toNat + 8 * k ≤ 2 ^ 64
  hn0p : n0p.toNat + 8 ≤ 2 ^ 64
  htp : tp.toNat + 8 * (k + 3) ≤ 2 ^ 64
  sepA : ap.toNat + 8 * k ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ ap.toNat
  sepB : bp.toNat + 8 * k ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ bp.toNat
  sepN : np.toNat + 8 * k ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ np.toNat
  sepN0 : n0p.toNat + 8 ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ n0p.toNat
  rA : ⟨ap, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rB : ⟨bp, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rN : ⟨np, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rN0 : ⟨n0p, 8⟩ ∈ s.vg.rd ++ s.vg.wr
  rT : ∃ L, 8 * (k + 3) ≤ L ∧ ⟨tp, L⟩ ∈ s.vg.wr

set_option maxHeartbeats 8000000 in
theorem first_ok (s : S) (j k : Nat) (ap bp np n0p tp b q cA cN : BitVec 64) (a n : Nat → BitVec 64)
    (hj : 1 ≤ j) (hjk : j + 7 ≤ k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp)
    (hr15 : s.vg.gpr .r15 = BitVec.ofNat 64 (j + 3)) (hrbx : s.vg.gpr .rbx = b) (hrbp : s.vg.gpr .rbp = q)
    (hr10 : s.vg.gpr .r10 = cA) (hr13 : s.vg.gpr .r13 = cN) (hrax : s.vg.gpr .rax = a (j + 1))
    (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i) :
    let w0 := step0 (a (j + 1)) (n (j + 1)) b q (cA, cN)
    let w1 := step0 (a (j + 2)) (n (j + 2)) b q w0.2
    let w2 := step0 (a (j + 3)) (n (j + 3)) b q w1.2
    let w3 := step0 (a (j + 4)) (n (j + 4)) b q w2.2
    ∃ s', execBlock I first s = some (s', firstTrace ap np tp j) ∧
      s'.vg.gpr .r10 = w3.2.1 ∧ s'.vg.gpr .r13 = w3.2.2 ∧ s'.vg.gpr .rax = a (j + 5) ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 (j + 7) ∧ s'.vg.cf = some (decide (j + 7 < k)) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa tp j) w0.1).writeW (wa tp (j + 1)) w1.1).writeW (wa tp (j + 2)) w2.1).writeW
        (wa tp (j + 3)) w3.1 ∧
      Frame s s' [.rax, .rdx, .rdi, .r10, .r11, .r13, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  intro w0 w1 w2 w3
  mul4x_block [first, hrsi, hrcx, hrsp, hr15, hrbx, hrbp, hr10, hr13, hrax, hr9, hA, hN]

def innerTrace (ap np tp : Addr) (j : Nat) : List Leak :=
  [.addr (wa np (j + 1)), .addr (wa tp (j + 1)), .addr (wa ap (j + 2)), .addr (wa tp j),
   .addr (wa np (j + 2)), .addr (wa tp (j + 2)), .addr (wa ap (j + 3)), .addr (wa tp (j + 1)),
   .addr (wa np (j + 3)), .addr (wa tp (j + 3)), .addr (wa ap (j + 4)), .addr (wa tp (j + 2)),
   .addr (wa np (j + 4)), .addr (wa tp (j + 4)), .addr (wa ap (j + 5)), .addr (wa tp (j + 3))]

set_option maxHeartbeats 8000000 in
theorem inner_ok (s : S) (j k : Nat) (ap bp np n0p tp b q cA cN : BitVec 64) (a n t : Nat → BitVec 64)
    (hj : 1 ≤ j) (hjk : j + 7 ≤ k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp)
    (hr15 : s.vg.gpr .r15 = BitVec.ofNat 64 (j + 3)) (hrbx : s.vg.gpr .rbx = b) (hrbp : s.vg.gpr .rbp = q)
    (hr10 : s.vg.gpr .r10 = cA) (hr13 : s.vg.gpr .r13 = cN) (hrax : s.vg.gpr .rax = a (j + 1))
    (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i, j + 1 ≤ i → i ≤ j + 4 → s.vg.mem.readW (wa tp i) 64 = t i) :
    let w0 := step (a (j + 1)) (n (j + 1)) (t (j + 1)) b q (cA, cN)
    let w1 := step (a (j + 2)) (n (j + 2)) (t (j + 2)) b q w0.2
    let w2 := step (a (j + 3)) (n (j + 3)) (t (j + 3)) b q w1.2
    let w3 := step (a (j + 4)) (n (j + 4)) (t (j + 4)) b q w2.2
    ∃ s', execBlock I Rind.X86_64.Mul4x.inner s = some (s', innerTrace ap np tp j) ∧
      s'.vg.gpr .r10 = w3.2.1 ∧ s'.vg.gpr .r13 = w3.2.2 ∧ s'.vg.gpr .rax = a (j + 5) ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 (j + 7) ∧ s'.vg.cf = some (decide (j + 7 < k)) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa tp j) w0.1).writeW (wa tp (j + 1)) w1.1).writeW (wa tp (j + 2)) w2.1).writeW
        (wa tp (j + 3)) w3.1 ∧
      Frame s s' [.rax, .rdx, .rdi, .r10, .r11, .r13, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  intro w0 w1 w2 w3
  mul4x_block [Rind.X86_64.Mul4x.inner, hrsi, hrcx, hrsp, hr15, hrbx, hrbp, hr10, hr13, hrax, hr9, hA, hN, hT]

def body0Trace (ap bp np n0p tp : Addr) (k : Nat) : List Leak :=
  [.addr (wa tp (k + 1)), .addr (wa tp (k + 2)), .addr n0p, .addr bp, .addr ap, .addr np,
   .addr (wa ap 1), .addr (wa np 1), .addr (wa ap 2), .addr tp]

set_option maxHeartbeats 8000000 in
theorem body0_ok (s : S) (k : Nat) (ap bp np n0p tp rp x n0' : BitVec 64) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrdx : s.vg.gpr .rdx = bp) (hrcx : s.vg.gpr .rcx = np)
    (hr8 : s.vg.gpr .r8 = n0p) (hrsp : s.vg.gpr .rsp = tp) (hrdi : s.vg.gpr .rdi = rp)
    (hrax : s.vg.gpr .rax = x) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hA0 : s.vg.mem.readW ap 64 = a 0) (hN0 : s.vg.mem.readW np 64 = n 0) (hB0 : s.vg.mem.readW bp 64 = bw 0)
    (hn0 : s.vg.mem.readW n0p 64 = n0') :
    let A0 := (mulLo (a 0) (bw 0), mulHi (a 0) (bw 0))
    let q := n0' * A0.1
    let N0 := mac (n 0) q A0.1
    let w1 := step0 (a 1) (n 1) (bw 0) q (A0.2, N0.2)
    ∃ s', execBlock I body0 s = some (s', body0Trace ap bp np n0p tp k) ∧
      s'.vg.gpr .r10 = w1.2.1 ∧ s'.vg.gpr .r13 = w1.2.2 ∧ s'.vg.gpr .rax = a 2 ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 4 ∧ s'.vg.gpr .r14 = 0 ∧ s'.vg.gpr .rbx = bw 0 ∧ s'.vg.gpr .rbp = q ∧
      s'.vg.gpr .r12 = bp ∧ s'.vg.gpr .r8 = n0' ∧
      s'.vg.mem = ((s.vg.mem.writeW (wa tp (k + 1)) x).writeW (wa tp (k + 2)) rp).writeW tp w1.1 ∧
      Frame s s' [.rax, .rdx, .rdi, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  intro A0 q N0 w1
  mul4x_block [body0, hrsi, hrdx, hrcx, hr8, hrsp, hrdi, hrax, hr9, hA, hN, hA0, hN0, hB0, hn0]

def firstTailTrace (ap np tp : Addr) (j : Nat) : List Leak :=
  [.addr (wa np (j + 1)), .addr (wa ap (j + 2)), .addr (wa tp j),
   .addr (wa np (j + 2)), .addr ap, .addr (wa tp (j + 1)), .addr (wa tp (j + 2)), .addr (wa tp (j + 3))]

set_option maxHeartbeats 8000000 in
theorem firstTail_ok (s : S) (j k i : Nat) (ap bp np n0p tp b q cA cN : BitVec 64) (a n : Nat → BitVec 64)
    (hj : 5 ≤ j) (hjk : j + 3 = k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp)
    (hr15 : s.vg.gpr .r15 = BitVec.ofNat 64 (j + 3)) (hrbx : s.vg.gpr .rbx = b) (hrbp : s.vg.gpr .rbp = q)
    (hr10 : s.vg.gpr .r10 = cA) (hr13 : s.vg.gpr .r13 = cN) (hrax : s.vg.gpr .rax = a (j + 1))
    (hr14 : s.vg.gpr .r14 = BitVec.ofNat 64 i)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hA0 : s.vg.mem.readW ap 64 = a 0) :
    let w0 := step0 (a (j + 1)) (n (j + 1)) b q (cA, cN)
    let w1 := step0 (a (j + 2)) (n (j + 2)) b q w0.2
    ∃ s', execBlock I firstTail s = some (s', firstTailTrace ap np tp j) ∧
      s'.vg.gpr .rax = a 0 ∧ s'.vg.gpr .r14 = BitVec.ofNat 64 (i + 1) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa tp j) w0.1).writeW (wa tp (j + 1)) w1.1).writeW (wa tp (j + 2))
        (top0 w1.2).1).writeW (wa tp (j + 3)) (top0 w1.2).2 ∧
      Frame s s' [.rax, .rdx, .rdi, .r10, .r11, .r13, .r14] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  intro w0 w1
  mul4x_block [firstTail, hrsi, hrcx, hrsp, hr15, hrbx, hrbp, hr10, hr13, hrax, hr14, hA, hN, hA0]

def outerTailTrace (ap np tp : Addr) (j k : Nat) : List Leak :=
  [.addr (wa np (j + 1)), .addr (wa tp (j + 1)), .addr (wa ap (j + 2)), .addr (wa tp j),
   .addr (wa np (j + 2)), .addr (wa tp (j + 2)), .addr ap, .addr (wa tp (j + 1)),
   .addr (wa tp k), .addr (wa tp (j + 2)), .addr (wa tp (j + 3))]

set_option maxHeartbeats 8000000 in
theorem outerTail_ok (s : S) (j k i : Nat) (ap bp np n0p tp b q cA cN : BitVec 64) (a n t : Nat → BitVec 64)
    (hj : 5 ≤ j) (hjk : j + 3 = k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp)
    (hr15 : s.vg.gpr .r15 = BitVec.ofNat 64 (j + 3)) (hrbx : s.vg.gpr .rbx = b) (hrbp : s.vg.gpr .rbp = q)
    (hr10 : s.vg.gpr .r10 = cA) (hr13 : s.vg.gpr .r13 = cN) (hrax : s.vg.gpr .rax = a (j + 1))
    (hr14 : s.vg.gpr .r14 = BitVec.ofNat 64 i) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k) (hi : i < k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hA0 : s.vg.mem.readW ap 64 = a 0)
    (hT : ∀ i, j + 1 ≤ i → i ≤ j + 3 → s.vg.mem.readW (wa tp i) 64 = t i) :
    let w0 := step (a (j + 1)) (n (j + 1)) (t (j + 1)) b q (cA, cN)
    let w1 := step (a (j + 2)) (n (j + 2)) (t (j + 2)) b q w0.2
    ∃ s', execBlock I outerTail s = some (s', outerTailTrace ap np tp j k) ∧
      s'.vg.gpr .rax = a 0 ∧ s'.vg.gpr .r14 = BitVec.ofNat 64 (i + 1) ∧
      s'.vg.cf = some (decide (i + 1 < k)) ∧
      s'.vg.mem = (((s.vg.mem.writeW (wa tp j) w0.1).writeW (wa tp (j + 1)) w1.1).writeW (wa tp (j + 2))
        (top w1.2 (t k)).1).writeW (wa tp (j + 3)) (top w1.2 (t k)).2 ∧
      Frame s s' [.rax, .rdx, .rdi, .r10, .r11, .r13, .r14] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  intro w0 w1
  mul4x_block [outerTail, hrsi, hrcx, hrsp, hr15, hrbx, hrbp, hr10, hr13, hrax, hr14, hr9, hA, hN, hA0, hT]

def outerHeadTrace (ap bp np tp : Addr) (i : Nat) : List Leak :=
  [.addr (wa bp i), .addr tp, .addr np, .addr (wa ap 1), .addr (wa np 1), .addr (wa tp 1), .addr (wa ap 2), .addr tp]

set_option maxHeartbeats 8000000 in
theorem outerHead_ok (s : S) (k i : Nat) (ap bp np n0p tp n0' : BitVec 64) (a bw n t : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hi : i < k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp)
    (hr12 : s.vg.gpr .r12 = bp) (hr8 : s.vg.gpr .r8 = n0') (hrax : s.vg.gpr .rax = a 0)
    (hr14 : s.vg.gpr .r14 = BitVec.ofNat 64 i)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s.vg.mem.readW (wa bp i) 64 = bw i) (hN0 : s.vg.mem.readW np 64 = n 0)
    (hT0 : s.vg.mem.readW tp 64 = t 0) (hT1 : s.vg.mem.readW (wa tp 1) 64 = t 1) :
    let A0 := mac (a 0) (bw i) (t 0)
    let q := n0' * A0.1
    let N0 := mac (n 0) q A0.1
    let w1 := step (a 1) (n 1) (t 1) (bw i) q (A0.2, N0.2)
    ∃ s', execBlock I outerHead s = some (s', outerHeadTrace ap bp np tp i) ∧
      s'.vg.gpr .r10 = w1.2.1 ∧ s'.vg.gpr .r13 = w1.2.2 ∧ s'.vg.gpr .rax = a 2 ∧
      s'.vg.gpr .r15 = BitVec.ofNat 64 4 ∧ s'.vg.gpr .rbx = bw i ∧ s'.vg.gpr .rbp = q ∧
      s'.vg.mem = s.vg.mem.writeW tp w1.1 ∧
      Frame s s' [.rax, .rdx, .rdi, .rbx, .rbp, .r10, .r11, .r13, .r15] := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  intro A0 q N0 w1
  mul4x_block [outerHead, hrsi, hrcx, hrsp, hr12, hr8, hrax, hr14, hA, hN, hB, hN0, hT0, hT1]

end rind.x86_64.mul4x
