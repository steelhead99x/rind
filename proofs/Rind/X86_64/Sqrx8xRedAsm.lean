import Rind.X86_64.Sqrx8xSpec
import Rind.X86_64.Mul4xLoop
import Rind.X86_64.Mul4xSub

/-! # bn_sqrx8x_internal's reduction blocks, run

Each block of the reduction run symbolically. The frame's words are a function `g` of their index from the
stack pointer: the slots at 1 to 6, and `t`'s word `i` at `i + 7`. A block's carry chains are the model functions
`innerF` and `redF`, whose sums `acct` proves. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- A sum of a word index and a displacement `disp_pos` split into words, folded back. -/
theorem ofNat_add_mul8 (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b * 8#64 = BitVec.ofNat 64 (a + b * 8) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod]

open Lean Meta Elab Tactic in
/-- Clears the hypotheses about the machine's state, as `clear_state` does, and those about its vector registers,
whose 128-bit values `bv_omega` would otherwise carry through every address bound. -/
elab "red_clear" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isConstOf ``VG.X86_64.State.gpr || e.isConstOf ``VG.Mem.readW ||
        e.isConstOf ``VG.X86_64.State.rd || e.isConstOf ``VG.X86_64.State.wr ||
        e.isConstOf ``VG.X86_64.State.cf || e.isConstOf ``VG.X86_64.State.of ||
        e.isConstOf ``VG.X86_64.State.xmm).isSome then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

set_option hygiene false in
/-- Discharges a reduction block's side conditions, as `sqrx_disch` does, clearing with `red_clear`. -/
macro "red_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem,
        wr_setMem]) <;>
     first
      | (refine inR (List.mem_append_right _ rF) ?_; simp only; red_clear; bv_omega)
      | (refine inR rF ?_; simp only; red_clear; bv_omega)
      | (refine inR rA ?_; simp only; red_clear; bv_omega)
      | (refine inR rN ?_; simp only; red_clear; bv_omega)
      | (unfold Apart; red_clear; constructor <;> bv_omega)
      | omega)

set_option hygiene false in
/-- Proves a reduction block's lemma, as `sqrx_block` does, with `imul`, `xor`, and `movq r64, xmm` too. -/
syntax "red_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| red_block [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      simp (config := { maxSteps := 4000000 }) (disch := red_disch) only [$xs,*, execAcc_cons, execAcc_nil,
        load64_of, store64_of, ↓exec_dec, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
        VG.X86_64.exec, execAlu, execAlu32, execMulx, execAdcx, execAdox, readSrc, readSrc32, Option.map_some,
        Option.bind_some, State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg,
        Int.reduceMod, Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb, ofNat_add_pos,
        ofNat_sub_ofNat, ofNat_add_mul8, BitVec.xor_self, BitVec.sub_self, BitVec.zero_add, BitVec.add_sub_cancel, BitVec.reduceSub,
        VG.X86_64.State.setReg32, setWidth_zero32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow,
        Nat.add_zero, ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero',
        readW_writeW_eq, readW_writeW_sep, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, of_setReg,
        gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, cf_arithFlags, of_arithFlags,
        gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, cf_setFlags, of_setFlags, gpr_setMem, mem_setMem,
        rd_setMem, wr_setMem, cf_setMem, of_setMem, zf_setReg, zf_setFlags, zf_arithFlags, zf_setMem, sf_setReg,
        sf_setFlags, sf_arithFlags, sf_setMem, gpr_execImul, mem_execImul, rd_execImul, wr_execImul,
        xmm_setReg, xmm_setFlags, xmm_arithFlags, xmm_setMem, xmm_execImul, extract_lo,
        fold_adcS, fold_adcC, fold_adcC', fold_addC, fold_addC', fold_mulLo, fold_mulHi, fold_mulHi',
        reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append,
        List.cons_append]
      rfl
    · rfl
    · repeat' apply And.intro
      all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
        others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags,
        gpr_setFlags, mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem,
        wr_setMem, xmm_setMem, others_setMem, gpr_execImul, mem_execImul, wr_execImul, xmm_execImul,
        others_execImul, cf_arithFlags, cf_setReg, cf_setFlags, cf_setMem, of_setReg, of_setFlags,
        of_arithFlags, of_setMem, zf_setReg, zf_setFlags, zf_arithFlags, zf_setMem, reduceCtorEq, ↓reduceIte, *]
      all_goals first
        | rfl
        | (simp only [wa]; red_clear; bv_omega)
        | skip))

/-! ## The first multiplier -/

/-- The words `redHead` reads: `t`'s seven past the window's first, then slot 4, which it writes. -/
def redHeadTrace (fp : Addr) (p : Nat) : List Leak :=
  [.addr (wa fp (p + 8)), .addr (wa fp (p + 9)), .addr (wa fp (p + 10)), .addr (wa fp (p + 11)),
   .addr (wa fp (p + 12)), .addr (wa fp (p + 13)), .addr (wa fp (p + 14)), .addr (wa fp 4)]

set_option maxHeartbeats 4000000 in
/-- `redHead` at the window from `t`'s word `p`: loads it into the accumulator, its first multiplier into `rdx`,
and saves the top carry `R` in slot 4. -/
theorem redHead_ok (s : S) (k p : Nat) (ap np fp d n0 R : BitVec 64) (g : Nat → BitVec 64)
    (hp : p + 8 ≤ 2 * k) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrdi : s.vg.gpr .rdi = wa fp (p + 7)) (hrdx : s.vg.gpr .rdx = d)
    (hrbx : s.vg.gpr .rbx = n0) (hrax : s.vg.gpr .rax = R)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.redHead s = some (s', redHeadTrace fp p) ∧
      s'.vg.gpr .r8 = d ∧ s'.vg.gpr .r9 = g (p + 8) ∧ s'.vg.gpr .r10 = g (p + 9) ∧
      s'.vg.gpr .r11 = g (p + 10) ∧ s'.vg.gpr .r12 = g (p + 11) ∧ s'.vg.gpr .r13 = g (p + 12) ∧
      s'.vg.gpr .r14 = g (p + 13) ∧ s'.vg.gpr .r15 = g (p + 14) ∧ s'.vg.gpr .rdx = d * n0 ∧
      s'.vg.gpr .rdi = wa fp (p + 15) ∧ s'.vg.gpr .rsi = 0 ∧ s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8) ∧
      s'.vg.cf = some false ∧ s'.vg.of = some false ∧ s'.vg.mem = s.vg.mem.writeW (wa fp 4) R ∧
      Frame s s' [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  red_block [Rind.X86_64.Sqrx8x.redHead, hrsp, hrdi, hrdx, hrbx, hrax, hG]

/-! ## The multipliers -/

/-- `red`'s run: the accumulator `r8..r15` plus `q` times `n0..n7`, its low word dropped, on two carry chains. -/
def redF (q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64) (cf of : Bool) : Row :=
  let c1 := adcC (mulLo q n0) r8 cf
  let t0 := adcS (mulHi q n0) r9 of
  let o1 := adcC (mulHi q n0) r9 of
  let c2 := adcC t0 (mulLo q n1) c1
  let t1 := adcS (mulHi q n1) r10 o1
  let o2 := adcC (mulHi q n1) r10 o1
  let c3 := adcC t1 (mulLo q n2) c2
  let t2 := adcS (mulHi q n2) r11 o2
  let o3 := adcC (mulHi q n2) r11 o2
  let c4 := adcC t2 (mulLo q n3) c3
  let t3 := adcS (mulHi q n3) r12 o3
  let o4 := adcC (mulHi q n3) r12 o3
  let c5 := adcC t3 (mulLo q n4) c4
  let t4 := adcS (mulHi q n4) r13 o4
  let o5 := adcC (mulHi q n4) r13 o4
  let c6 := adcC t4 (mulLo q n5) c5
  let t5 := adcS (mulHi q n5) r14 o5
  let o6 := adcC (mulHi q n5) r14 o5
  let c7 := adcC t5 (mulLo q n6) c6
  let t6 := adcS (mulHi q n6) r15 o6
  let o7 := adcC (mulHi q n6) r15 o6
  let c8 := adcC t6 (mulLo q n7) c7
  let t7 := adcS (mulHi q n7) 0 o7
  let o8 := adcC (mulHi q n7) 0 o7
  let c9 := adcC t7 0 c8
  { w := adcS (mulLo q n0) r8 cf, r8 := adcS t0 (mulLo q n1) c1, r9 := adcS t1 (mulLo q n2) c2,
    r10 := adcS t2 (mulLo q n3) c3, r11 := adcS t3 (mulLo q n4) c4, r12 := adcS t4 (mulLo q n5) c5,
    r13 := adcS t5 (mulLo q n6) c6, r14 := adcS t6 (mulLo q n7) c7, r15 := adcS t7 0 c8, cf := c9, of := o8 }

theorem redF_acct (q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64) (cf of : Bool) :
    let F := redF q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 cf of
    hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] + 2 ^ 576 * (F.cf.toNat + F.of.toNat) =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] +
        cf.toNat + 2 ^ 64 * of.toNat := by
  simp only [redF, hsum, BitVec.toNat_ofNat, Nat.zero_mod]
  acct

/-- The low word a Montgomery step drops: `r + (r·m mod 2^64)·n`, for `m = -n⁻¹ mod 2^64`, is a multiple of
`2^64`. -/
theorem redc_zero (r m n : Nat) (h : (n * m + 1) % 2 ^ 64 = 0) : (r * m % 2 ^ 64 * n % 2 ^ 64 + r) % 2 ^ 64 = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  rw [← ZMod.natCast_eq_zero_iff]
  have h' := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h)
  push_cast [ZMod.natCast_mod] at h' ⊢
  linear_combination (r : ZMod (2 ^ 64)) * h'

/-- The trace of `red`'s run `j`: `n`'s first eight words, `n0` in slot 5, and the multiplier's word of `t`. -/
def redTraceJ (np fp : Addr) (j : Nat) : List Leak :=
  [.addr np, .addr (wa np 1), .addr (wa np 2), .addr (wa np 3), .addr (wa np 4), .addr (wa fp 5),
   .addr (wa fp (7 + j)), .addr (wa np 5), .addr (wa np 6), .addr (wa np 7)]

set_option maxHeartbeats 4000000 in
/-- A run of `red`: adds `q` times `n`'s first eight words to the accumulator, drops its low word, stores `q` at
`t`'s word `j`, and takes the next multiplier from the new low word and slot 5's `n0`. -/
theorem redBlock_ok (s : S) (k j : Nat) (ap np fp q : BitVec 64) (n g : Nat → BitVec 64)
    (hj : j < 8) (hk : 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrbp : s.vg.gpr .rbp = np) (hrdx : s.vg.gpr .rdx = q)
    (hrsi : s.vg.gpr .rsi = 0) (hq : fp + (s.vg.gpr .rcx + 15#64) * 8#64 = wa fp (7 + j))
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false)
    (hN0 : s.vg.mem.readW np 64 = n 0) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    let F := redF q (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (s.vg.gpr .r8) (s.vg.gpr .r9)
      (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) false false
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.red s = some (s', redTraceJ np fp j) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp (7 + j)) q ∧
      s'.vg.gpr .rcx = s.vg.gpr .rcx + 1 ∧ s'.vg.gpr .rdx = mulLo F.r8 (g 5) ∧ s'.vg.gpr .rsi = 0 ∧
      s'.vg.gpr .r8 = F.r8 ∧ s'.vg.gpr .r9 = F.r9 ∧ s'.vg.gpr .r10 = F.r10 ∧ s'.vg.gpr .r11 = F.r11 ∧
      s'.vg.gpr .r12 = F.r12 ∧ s'.vg.gpr .r13 = F.r13 ∧ s'.vg.gpr .r14 = F.r14 ∧ s'.vg.gpr .r15 = F.r15 ∧
      s'.vg.cf = some F.cf ∧ s'.vg.zf = some (s.vg.gpr .rcx + 1 == 0) ∧
      s'.vg.of = some (addOverflow (s.vg.gpr .rcx) 1 (s.vg.gpr .rcx + 1)) ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro F
  red_block [Rind.X86_64.Sqrx8x.red, hrsp, hrbp, hrdx, hrsi, hq, hcf, hof, hN0, hN, hG]

/-! ## Eight-word sums -/

/-- An accumulator of eight words and its carry. -/
structure Acc where
  r8 : BitVec 64
  r9 : BitVec 64
  r10 : BitVec 64
  r11 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  c : Bool

/-- `x + y + c` on eight words, `adc`'s chain. -/
def add8 (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : BitVec 64) (c : Bool) : Acc :=
  let c1 := adcC x0 y0 c
  let c2 := adcC x1 y1 c1
  let c3 := adcC x2 y2 c2
  let c4 := adcC x3 y3 c3
  let c5 := adcC x4 y4 c4
  let c6 := adcC x5 y5 c5
  let c7 := adcC x6 y6 c6
  { r8 := adcS x0 y0 c, r9 := adcS x1 y1 c1, r10 := adcS x2 y2 c2, r11 := adcS x3 y3 c3,
    r12 := adcS x4 y4 c4, r13 := adcS x5 y5 c5, r14 := adcS x6 y6 c6, r15 := adcS x7 y7 c7,
    c := adcC x7 y7 c7 }

/-- `x + y` on eight words, an `add` then `adc`s. -/
def add8' (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : BitVec 64) : Acc :=
  let c1 := addC x0 y0
  let c2 := adcC x1 y1 c1
  let c3 := adcC x2 y2 c2
  let c4 := adcC x3 y3 c3
  let c5 := adcC x4 y4 c4
  let c6 := adcC x5 y5 c5
  let c7 := adcC x6 y6 c6
  { r8 := x0 + y0, r9 := adcS x1 y1 c1, r10 := adcS x2 y2 c2, r11 := adcS x3 y3 c3,
    r12 := adcS x4 y4 c4, r13 := adcS x5 y5 c5, r14 := adcS x6 y6 c6, r15 := adcS x7 y7 c7,
    c := adcC x7 y7 c7 }

/-- An accumulator's value. -/
def Acc.val (A : Acc) : Nat := hsum [A.r8, A.r9, A.r10, A.r11, A.r12, A.r13, A.r14, A.r15]

theorem add8_acct (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : BitVec 64) (c : Bool) :
    let A := add8 x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 c
    A.val + 2 ^ 512 * A.c.toNat =
      hsum [x0, x1, x2, x3, x4, x5, x6, x7] + hsum [y0, y1, y2, y3, y4, y5, y6, y7] + c.toNat := by
  simp only [add8, Acc.val, hsum]
  acct

theorem add8'_acct (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : BitVec 64) :
    let A := add8' x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7
    A.val + 2 ^ 512 * A.c.toNat =
      hsum [x0, x1, x2, x3, x4, x5, x6, x7] + hsum [y0, y1, y2, y3, y4, y5, y6, y7] := by
  simp only [add8', Acc.val, hsum]
  acct

/-- The mask `sbb r, r` leaves of a carry. -/
def mask (c : Bool) : BitVec 64 := 0 - (BitVec.ofBool c).setWidth 64

/-- The carry `sub r, m` leaves from zero: whether `m` is not zero. -/
def unmask (m : BitVec 64) : Bool := decide ((0 : BitVec 64).toNat < m.toNat)

theorem unmask_mask (c : Bool) : unmask (mask c) = c := by cases c <;> decide

/-! ## The products with the rest of `n` -/

/-- The words `redEnd` reads: slot 1. -/
def redEndTrace (fp : Addr) : List Leak := [.addr (wa fp 1)]

set_option maxHeartbeats 4000000 in
/-- `redEnd`: clears `rax` from `rsi`, and compares `rbp` with slot 1. -/
theorem redEnd_ok (s : S) (k : Nat) (ap np fp : BitVec 64) (g : Nat → BitVec 64) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrsi : s.vg.gpr .rsi = 0)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.redEnd s = some (s', redEndTrace fp) ∧
      s'.vg.gpr .rax = 0 ∧ s'.vg.cf = some (decide ((s.vg.gpr .rbp).toNat < (g 1).toNat)) ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.rax] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  red_block [Rind.X86_64.Sqrx8x.redEnd, hrsp, hrsi, hG]

/-- The words `tailHead` reads: `t`'s first, the multiplier `q0`, the next eight of the window, and slot 3, which
it writes. -/
def tailHeadTrace (fp : Addr) (d : Nat) : List Leak :=
  [.addr (wa fp 7), .addr (wa fp d), .addr (wa fp (d + 1)), .addr (wa fp (d + 2)), .addr (wa fp (d + 3)),
   .addr (wa fp (d + 4)), .addr (wa fp (d + 5)), .addr (wa fp (d + 6)), .addr (wa fp (d + 7)), .addr (wa fp 3)]

set_option maxHeartbeats 4000000 in
/-- `tailHead`, `rdi` at the frame's word `d`: adds the eight words there to the accumulator, keeps their carry's
mask in slot 3, loads `q0`, and steps `rbp` to `n`'s next eight words. -/
theorem tailHead_ok (s : S) (k d : Nat) (ap np fp : BitVec 64) (g : Nat → BitVec 64)
    (hd : d + 8 ≤ 2 * k + 9) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrdi : s.vg.gpr .rdi = wa fp d) (hrbp : s.vg.gpr .rbp = np)
    (hrax : s.vg.gpr .rax = 0)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    let A := add8' (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) (g d) (g (d + 1)) (g (d + 2)) (g (d + 3)) (g (d + 4))
      (g (d + 5)) (g (d + 6)) (g (d + 7))
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tailHead s = some (s', tailHeadTrace fp d) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp 3) (mask A.c) ∧
      s'.vg.gpr .r8 = A.r8 ∧ s'.vg.gpr .r9 = A.r9 ∧ s'.vg.gpr .r10 = A.r10 ∧ s'.vg.gpr .r11 = A.r11 ∧
      s'.vg.gpr .r12 = A.r12 ∧ s'.vg.gpr .r13 = A.r13 ∧ s'.vg.gpr .r14 = A.r14 ∧ s'.vg.gpr .r15 = A.r15 ∧
      s'.vg.gpr .rdx = g 7 ∧ s'.vg.gpr .rbp = wa np 8 ∧ s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8) ∧
      s'.vg.gpr .rdi = wa fp (d + 8) ∧ s'.vg.gpr .rsi = 0 ∧ s'.vg.cf = some false ∧ s'.vg.of = some false ∧
      Frame s s' [.rax, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro A
  red_block [Rind.X86_64.Sqrx8x.tailHead, hrsp, hrdi, hrbp, hrax, hG]

/-- The trace of `tail`'s run `j`, at `n`'s word `c` and `t`'s frame word `d`. -/
def tailTraceJ (np fp : Addr) (c d j : Nat) : List Leak :=
  [.addr (wa np c), .addr (wa np (c + 1)), .addr (wa np (c + 2)), .addr (wa np (c + 3)), .addr (wa np (c + 4)),
   .addr (wa np (c + 5)), .addr (wa np (c + 6)), .addr (wa np (c + 7)), .addr (wa fp (8 + j)), .addr (wa fp d)]

set_option maxHeartbeats 4000000 in
/-- A run of `tail`: adds `q` times `n`'s eight words from `c` to the accumulator, stores its low word at the frame's
word `d`, and loads the next multiplier, `t`'s word `j + 1`. -/
theorem redTail_ok (s : S) (k c d j : Nat) (ap np fp q : BitVec 64) (n g : Nat → BitVec 64)
    (hj : j < 8) (hc : c + 8 ≤ k) (hd : d < 2 * k + 9) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrbp : s.vg.gpr .rbp = wa np c) (hrdx : s.vg.gpr .rdx = q)
    (hrsi : s.vg.gpr .rsi = 0)
    (hst : s.vg.gpr .rdi + s.vg.gpr .rcx * 8#64 = wa fp d)
    (hld : fp + (s.vg.gpr .rcx + 2#64 * 8#64) * 8#64 = wa fp (8 + j))
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false)
    (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    let F := innerF q (n c) (n (c + 1)) (n (c + 2)) (n (c + 3)) (n (c + 4)) (n (c + 5)) (n (c + 6)) (n (c + 7))
      (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13)
      (s.vg.gpr .r14) (s.vg.gpr .r15) false false
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tail s = some (s', tailTraceJ np fp c d j) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp d) F.w ∧
      s'.vg.gpr .rcx = s.vg.gpr .rcx + 1 ∧ s'.vg.gpr .rdx = g (8 + j) ∧ s'.vg.gpr .rsi = 0 ∧
      s'.vg.gpr .r8 = F.r8 ∧ s'.vg.gpr .r9 = F.r9 ∧ s'.vg.gpr .r10 = F.r10 ∧ s'.vg.gpr .r11 = F.r11 ∧
      s'.vg.gpr .r12 = F.r12 ∧ s'.vg.gpr .r13 = F.r13 ∧ s'.vg.gpr .r14 = F.r14 ∧ s'.vg.gpr .r15 = F.r15 ∧
      s'.vg.cf = some F.cf ∧ s'.vg.zf = some (s.vg.gpr .rcx + 1 == 0) ∧
      s'.vg.of = some (addOverflow (s.vg.gpr .rcx) 1 (s.vg.gpr .rcx + 1)) ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro F
  red_block [Rind.X86_64.Sqrx8x.tail, hrsp, hrbp, hrdx, hrsi, hst, hld, hcf, hof, hN, hG]

/-- The words `tailEnd` reads: slot 1. -/
def tailEndTrace (fp : Addr) : List Leak := [.addr (wa fp 1)]

set_option maxHeartbeats 4000000 in
/-- `tailEnd`: compares `rbp` with slot 1. -/
theorem tailEnd_ok (s : S) (k : Nat) (ap np fp : BitVec 64) (g : Nat → BitVec 64) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tailEnd s = some (s', tailEndTrace fp) ∧
      s'.vg.cf = some (decide ((s.vg.gpr .rbp).toNat < (g 1).toNat)) ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  red_block [Rind.X86_64.Sqrx8x.tailEnd, hrsp, hG]

/-- The words `tailNext` reads: slot 3, `q0`, the next eight of the window, and slot 3, which it writes. -/
def tailNextTrace (fp : Addr) (d : Nat) : List Leak :=
  [.addr (wa fp 3), .addr (wa fp 7), .addr (wa fp d), .addr (wa fp (d + 1)), .addr (wa fp (d + 2)),
   .addr (wa fp (d + 3)), .addr (wa fp (d + 4)), .addr (wa fp (d + 5)), .addr (wa fp (d + 6)),
   .addr (wa fp (d + 7)), .addr (wa fp 3)]

set_option maxHeartbeats 4000000 in
/-- `tailNext`, `rdi` at the frame's word `d`: adds the eight words there and slot 3's carry to the accumulator,
keeps their carry's mask in slot 3, loads `q0`, and steps `rbp` on eight words of `n`. -/
theorem tailNext_ok (s : S) (k c d : Nat) (ap np fp : BitVec 64) (g : Nat → BitVec 64)
    (hd : d + 8 ≤ 2 * k + 9) (hc : c + 16 ≤ k) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrdi : s.vg.gpr .rdi = wa fp d) (hrbp : s.vg.gpr .rbp = wa np c)
    (hrsi : s.vg.gpr .rsi = 0) (hrcx : s.vg.gpr .rcx = 0)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    let A := add8 (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) (g d) (g (d + 1)) (g (d + 2)) (g (d + 3)) (g (d + 4))
      (g (d + 5)) (g (d + 6)) (g (d + 7)) (unmask (g 3))
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tailNext s = some (s', tailNextTrace fp d) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp 3) (mask A.c) ∧
      s'.vg.gpr .r8 = A.r8 ∧ s'.vg.gpr .r9 = A.r9 ∧ s'.vg.gpr .r10 = A.r10 ∧ s'.vg.gpr .r11 = A.r11 ∧
      s'.vg.gpr .r12 = A.r12 ∧ s'.vg.gpr .r13 = A.r13 ∧ s'.vg.gpr .r14 = A.r14 ∧ s'.vg.gpr .r15 = A.r15 ∧
      s'.vg.gpr .rdx = g 7 ∧ s'.vg.gpr .rbp = wa np (c + 8) ∧ s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8) ∧
      s'.vg.gpr .rdi = wa fp (d + 8) ∧ s'.vg.gpr .rsi = 0 ∧ s'.vg.cf = some false ∧ s'.vg.of = some false ∧
      Frame s s' [.rax, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro A
  red_block [Rind.X86_64.Sqrx8x.tailNext, hrsp, hrdi, hrbp, hrsi, hrcx, hG]

/-- The words `tailDone` reads: slots 4 and 3. -/
def tailDoneTrace (fp : Addr) : List Leak := [.addr (wa fp 4), .addr (wa fp 3)]

set_option maxHeartbeats 4000000 in
/-- `tailDone`: adds slot 4's top carry to the accumulator, its carry into `rax`, and takes slot 3's carry. -/
theorem tailDone_ok (s : S) (k : Nat) (ap np fp : BitVec 64) (g : Nat → BitVec 64) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrsi : s.vg.gpr .rsi = 0)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    let A := add8' (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) (g 4) 0 0 0 0 0 0 0
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tailDone s = some (s', tailDoneTrace fp) ∧
      s'.vg.mem = s.vg.mem ∧
      s'.vg.gpr .r8 = A.r8 ∧ s'.vg.gpr .r9 = A.r9 ∧ s'.vg.gpr .r10 = A.r10 ∧ s'.vg.gpr .r11 = A.r11 ∧
      s'.vg.gpr .r12 = A.r12 ∧ s'.vg.gpr .r13 = A.r13 ∧ s'.vg.gpr .r14 = A.r14 ∧ s'.vg.gpr .r15 = A.r15 ∧
      s'.vg.gpr .rax = (BitVec.ofBool A.c).setWidth 64 ∧ s'.vg.cf = some (unmask (g 3)) ∧
      Frame s s' [.rax, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro A
  red_block [Rind.X86_64.Sqrx8x.tailDone, hrsp, hrsi, hG]

/-! ## The round's last words -/

/-- The words `noTail` reads and writes, `rdi` at the frame's word `e`: the eight there, `n`'s last, slot 5, the
next round's first word, the eight again, and slot 2. -/
def noTailTrace (np fp : Addr) (k e : Nat) : List Leak :=
  [.addr (wa fp e), .addr (wa fp (e + 1)), .addr (wa np (k - 8 + 7)), .addr (wa fp (e + 2)),
   .addr (wa fp (e + 3)), .addr (wa fp (e + 4)), .addr (wa fp (e + 5)), .addr (wa fp (e + 6)),
   .addr (wa fp (e + 7)), .addr (wa fp 5), .addr (wa fp (e + 8 - k)), .addr (wa fp e), .addr (wa fp (e + 1)),
   .addr (wa fp (e + 2)), .addr (wa fp (e + 3)), .addr (wa fp (e + 4)), .addr (wa fp (e + 5)),
   .addr (wa fp (e + 6)), .addr (wa fp (e + 7)), .addr (wa fp 2)]

/-- The memory `noTail` leaves: the accumulator's eight words at the frame's word `e`. -/
abbrev store8 (M : Mem) (fp : Addr) (e : Nat) (A : Acc) : Mem :=
  (((((((M.writeW (wa fp e) A.r8).writeW (wa fp (e + 1)) A.r9).writeW (wa fp (e + 2)) A.r10).writeW
    (wa fp (e + 3)) A.r11).writeW (wa fp (e + 4)) A.r12).writeW (wa fp (e + 5)) A.r13).writeW
    (wa fp (e + 6)) A.r14).writeW (wa fp (e + 7)) A.r15

set_option maxHeartbeats 4000000 in
/-- `noTail`, `rdi` at the frame's word `e`: adds the eight words there and the carry to the accumulator, its carry
into `rax`, stores it there, steps `rdi` back to the next round's window, loads its first word, and compares the
end of what it stored with slot 2. -/
theorem noTail_ok (s : S) (k e : Nat) (ap np fp R : BitVec 64) (n g : Nat → BitVec 64) (cf : Bool)
    (hk : 8 ≤ k) (hke : k ≤ e) (he : e + 8 ≤ 2 * k + 9) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrdi : s.vg.gpr .rdi = wa fp e) (hrbp : s.vg.gpr .rbp = wa np (k - 8))
    (hrax : s.vg.gpr .rax = R) (hcf : s.vg.cf = some cf)
    (hx2 : (s.vg.xmm .xmm2).setWidth 64 = np)
    (hrd : wa fp e + (s.vg.xmm .xmm3).setWidth 64 * 1#64 + 8#64 * 8#64 = wa fp (e + 8 - k))
    (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hG : ∀ i < 2 * k + 9, s.vg.mem.readW (wa fp i) 64 = g i) :
    let A := add8 (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) (g e) (g (e + 1)) (g (e + 2)) (g (e + 3)) (g (e + 4))
      (g (e + 5)) (g (e + 6)) (g (e + 7)) cf
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.noTail s = some (s', noTailTrace np fp k e) ∧
      s'.vg.mem = store8 s.vg.mem fp e A ∧
      s'.vg.gpr .rax = adcS R 0 A.c ∧
      s'.vg.gpr .rcx = (s.vg.xmm .xmm3).setWidth 64 ∧ s'.vg.gpr .rbp = np ∧ s'.vg.gpr .rbx = g 5 ∧
      s'.vg.gpr .rdx = g (e + 8 - k) ∧ s'.vg.gpr .r8 = wa fp (e + 8) ∧ s'.vg.gpr .rdi = wa fp (e + 8 - k) ∧
      s'.vg.cf = some (decide ((wa fp (e + 8)).toNat < (g 2).toNat)) ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro A
  red_block [Rind.X86_64.Sqrx8x.noTail, Nat.one_mul, hrsp, hrdi, hrbp, hrax, hcf, hx2, hrd, hN, hG]

end rind.x86_64.sqrx8x
