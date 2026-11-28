import RindIsa.X86_64.Sqrx8x
import Rind.X86_64.Acct
import Rind.X86_64.Mulx4xAsm

/-! # bn_sqrx8x_internal's blocks, run

Each block run symbolically: the words it stores, and the registers and flags it leaves, related to those it
reads by `acct`'s linear arithmetic over its products. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

section
variable (s : VG.X86_64.State)
@[simp] theorem sf_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).sf = s.sf := rfl
@[simp] theorem sf_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).sf = d := rfl
@[simp] theorem sf_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).sf = some x.msb := rfl
@[simp] theorem sf_setMem (m : Mem) : (setMem s m).sf = s.sf := rfl
end

/-- The value of words, least significant first. -/
def hsum : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ 64 * hsum xs

/-- The memory a block reaches: `k` words of `a` and `n`, which it may read, and the frame's `2k + 9` words at
`fp`, the stack pointer: the return address, five slots, `n0`, and `t`'s `2k + 2` words, which it may write; the
frame overlaps neither of the others, and none wraps. -/
structure Arr (s : S) (k : Nat) (ap np fp : Addr) : Prop where
  k29 : k < 2 ^ 29
  hap : ap.toNat + 8 * k ≤ 2 ^ 64
  hnp : np.toNat + 8 * k ≤ 2 ^ 64
  hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64
  sepA : ap.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ ap.toNat
  sepN : np.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ np.toNat
  rA : ⟨ap, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rN : ⟨np, 8 * k⟩ ∈ s.vg.rd ++ s.vg.wr
  rF : ∃ L, 8 * (2 * k + 9) ≤ L ∧ ⟨fp, L⟩ ∈ s.vg.wr

theorem Arr.frame {s s' : S} {k : Nat} {ap np fp : Addr} {gs : List Reg} (ar : Arr s k ap np fp)
    (h : Frame s s' gs) : Arr s' k ap np fp := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, rF⟩ := ar
  rw [← h.rd, ← h.wr] at rA rN
  rw [← h.wr] at rF
  exact ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, rF⟩

/-- An XMM register's low half, as `movq` reads it. -/
theorem extract_lo (x : BitVec 128) : x.extractLsb' 0 64 = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]

theorem rcx_of (j : Nat) (h : j < 8) :
    addOverflow (BitVec.ofNat 64 (2 ^ 64 - 8 + j)) 1 (BitVec.ofNat 64 (2 ^ 64 - 8 + j) + 1) = false := by
  interval_cases j <;> decide

theorem gsum_split (g : Nat → Nat) (m n : Nat) :
    gsum g (m + n) = gsum g m + 2 ^ (64 * m) * gsum (fun i => g (m + i)) n := by
  induction n with
  | zero => simp [gsum]
  | succ n ih =>
    rw [← Nat.add_assoc, gsum, gsum, ih, show 64 * (m + n) = 64 * m + 64 * n by ring, Nat.pow_add]
    ring

/-- Splits a value at word `m`. -/
theorem val_split (f : Nat → BitVec 64) (m n : Nat) :
    val f (m + n) = val f m + 2 ^ (64 * m) * val (fun i => f (m + i)) n := gsum_split _ m n

open Lean Meta Elab Tactic in
/-- Clears the hypotheses about the machine's state, which `bv_omega` would otherwise case split on to no use:
an address's bounds take only the arrays' bounds and the indices'. -/
elab "clear_state" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isConstOf ``VG.X86_64.State.gpr || e.isConstOf ``VG.Mem.readW ||
        e.isConstOf ``VG.X86_64.State.rd || e.isConstOf ``VG.X86_64.State.wr ||
        e.isConstOf ``VG.X86_64.State.cf || e.isConstOf ``VG.X86_64.State.of).isSome then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

/-- Words `i` of `p` and `j` of `q`, neither wrapping, are apart if one ends before the other starts. -/
theorem apart_wa (p q : Addr) (i j : Nat) (hp : p.toNat + 8 * i + 8 ≤ 2 ^ 64) (hq : q.toNat + 8 * j + 8 ≤ 2 ^ 64)
    (h : p.toNat + 8 * i + 8 ≤ q.toNat + 8 * j ∨ q.toNat + 8 * j + 8 ≤ p.toNat + 8 * i) :
    Apart (p + BitVec.ofNat 64 i * 8#64) (q + BitVec.ofNat 64 j * 8#64) := by
  have ha : (p + BitVec.ofNat 64 i * 8#64).toNat = p.toNat + 8 * i := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have hb : (q + BitVec.ofNat 64 j * 8#64).toNat = q.toNat + 8 * j := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  unfold Apart
  rw [BitVec.toNat_sub, BitVec.toNat_sub, ha, hb]
  omega

set_option hygiene false in
/-- Discharges the side conditions of a block's run. -/
macro "sqrx_disch" : tactic => `(tactic| no_recover first
  | decide
  | (try simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem,
        wr_setMem]) <;>
     first
      | (refine inR (List.mem_append_right _ rF) ?_; simp only; clear_state; bv_omega)
      | (refine inR rF ?_; simp only; clear_state; bv_omega)
      | (refine inR rA ?_; simp only; clear_state; bv_omega)
      | (refine inR rN ?_; simp only; clear_state; bv_omega)
      | (apply apart_wa <;> omega)
      | (unfold Apart; clear_state; constructor <;> bv_omega)
      | omega)

/-- The lemmas that run a block of this routine, folding its sums and products into `acct`'s terms. -/
syntax "sqrx_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sqrx_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := sqrx_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, store64_of, ↓exec_dec, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, execAlu32, execMulx, execAdcx, execAdox, readSrc, readSrc32, Option.map_some,
      Option.bind_some, State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod,
      Int.reduceToNat, Int.reducePow, ea_pos, ea_neg, disp_pos, ea_comb, ofNat_add_pos, ofNat_sub_ofNat,
      BitVec.add_sub_cancel, BitVec.reduceSub,
      VG.X86_64.State.setReg32, setWidth_zero32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow,
      Nat.add_zero, ofNat_zero, BitVec.add_zero, add_zero', zero_add', signExtend_zero, signExtend_zero',
      readW_writeW_eq, readW_writeW_sep, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, of_setReg,
      gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, cf_arithFlags, of_arithFlags, gpr_setFlags,
      mem_setFlags, rd_setFlags, wr_setFlags, cf_setFlags, of_setFlags, gpr_setMem, mem_setMem, rd_setMem, wr_setMem,
      cf_setMem, of_setMem, zf_setReg, zf_setFlags, zf_arithFlags, zf_setMem, sf_setReg,
      sf_setFlags, sf_arithFlags, sf_setMem, fold_adcS, fold_adcC, fold_adcC', fold_addC, fold_addC', fold_mulLo, fold_mulHi,
      fold_mulHi', reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append,
      List.cons_append])

/-- Proves a block's lemma: runs it, matches the trace, reads the registers, flags, and memory it leaves, and
proves its sums by `acct`. -/
syntax "sqrx_block " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sqrx_block [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      sqrx_run [$xs,*]
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
        | (simp only [hsum]; acct_name; linarith)
        | skip))

/-! ## The squaring's inner loop -/

/-- What a run of `inner` leaves: the word it stores, the accumulator's eight words, and the carries. -/
structure Row where
  w : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  r10 : BitVec 64
  r11 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  cf : Bool
  of : Bool

/-- `inner`'s run: the accumulator `r8..r15` plus `x` times `a0..a7`, its low word out, on two carry
chains. -/
def innerF (x a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64) (cf of : Bool) : Row :=
  let c1 := adcC r8 (mulLo x a0) cf
  let t0 := adcS (mulHi x a0) r9 of
  let o1 := adcC (mulHi x a0) r9 of
  let c2 := adcC t0 (mulLo x a1) c1
  let t1 := adcS (mulHi x a1) r10 o1
  let o2 := adcC (mulHi x a1) r10 o1
  let c3 := adcC t1 (mulLo x a2) c2
  let t2 := adcS (mulHi x a2) r11 o2
  let o3 := adcC (mulHi x a2) r11 o2
  let c4 := adcC t2 (mulLo x a3) c3
  let t3 := adcS (mulHi x a3) r12 o3
  let o4 := adcC (mulHi x a3) r12 o3
  let c5 := adcC t3 (mulLo x a4) c4
  let t4 := adcS (mulHi x a4) r13 o4
  let o5 := adcC (mulHi x a4) r13 o4
  let c6 := adcC t4 (mulLo x a5) c5
  let t5 := adcS (mulHi x a5) r14 o5
  let o6 := adcC (mulHi x a5) r14 o5
  let c7 := adcC t5 (mulLo x a6) c6
  let t6 := adcS (mulHi x a6) r15 o6
  let o7 := adcC (mulHi x a6) r15 o6
  let c8 := adcC t6 (mulLo x a7) c7
  let t7 := adcS (mulHi x a7) 0 o7
  let o8 := adcC (mulHi x a7) 0 o7
  let c9 := adcC t7 0 c8
  { w := adcS r8 (mulLo x a0) cf, r8 := adcS t0 (mulLo x a1) c1, r9 := adcS t1 (mulLo x a2) c2,
    r10 := adcS t2 (mulLo x a3) c3, r11 := adcS t3 (mulLo x a4) c4, r12 := adcS t4 (mulLo x a5) c5,
    r13 := adcS t5 (mulLo x a6) c6, r14 := adcS t6 (mulLo x a7) c7, r15 := adcS t7 0 c8, cf := c9, of := o8 }

theorem innerF_acct (x a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64) (cf of : Bool) :
    let F := innerF x a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r10 r11 r12 r13 r14 r15 cf of
    hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] + 2 ^ 576 * (F.cf.toNat + F.of.toNat) =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + x.toNat * hsum [a0, a1, a2, a3, a4, a5, a6, a7] +
        cf.toNat + 2 ^ 64 * of.toNat := by
  simp only [innerF, hsum, BitVec.toNat_ofNat, Nat.zero_mod]
  acct

/-- The words `inner` reads from `a`: the eight from `c`, then the next row's multiplier. -/
def innerTrace (ap fp : Addr) (c d n : Nat) : List Leak :=
  [.addr (wa ap c), .addr (wa ap (c + 1)), .addr (wa ap (c + 2)), .addr (wa ap (c + 3)), .addr (wa ap (c + 4)),
   .addr (wa ap (c + 5)), .addr (wa ap (c + 6)), .addr (wa fp d), .addr (wa ap (c + 7)), .addr (wa ap n)]

set_option maxHeartbeats 4000000 in
/-- A run of `inner`: adds `x` times `a`'s eight words from `c` to the accumulator, storing its low word at `t`'s
`d`, and loads `a`'s word `n`, both indexed by `rcx`. -/
theorem inner_ok (s : S) (k c d n : Nat) (ap np fp x : BitVec 64) (cf of : Bool) (a : Nat → BitVec 64)
    (hc : c + 8 ≤ k) (hn : n < k) (hd : d < 2 * k + 9) (ar : Arr s k ap np fp)
    (hrbp : s.vg.gpr .rbp = wa ap c) (hrdx : s.vg.gpr .rdx = x)
    (hst : s.vg.gpr .rdi + s.vg.gpr .rcx * 8#64 = wa fp d)
    (hld : s.vg.gpr .rsi + (s.vg.gpr .rcx + 1#64) * 8#64 = wa ap n)
    (hcf : s.vg.cf = some cf) (hof : s.vg.of = some of)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) :
    let F := innerF x (a c) (a (c + 1)) (a (c + 2)) (a (c + 3)) (a (c + 4)) (a (c + 5)) (a (c + 6)) (a (c + 7))
      (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13)
      (s.vg.gpr .r14) (s.vg.gpr .r15) cf of
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.inner s = some (s', innerTrace ap fp c d n) ∧
      s'.vg.gpr .rcx = s.vg.gpr .rcx + 1 ∧ s'.vg.gpr .rdx = a n ∧
      s'.vg.gpr .r8 = F.r8 ∧ s'.vg.gpr .r9 = F.r9 ∧ s'.vg.gpr .r10 = F.r10 ∧ s'.vg.gpr .r11 = F.r11 ∧
      s'.vg.gpr .r12 = F.r12 ∧ s'.vg.gpr .r13 = F.r13 ∧ s'.vg.gpr .r14 = F.r14 ∧ s'.vg.gpr .r15 = F.r15 ∧
      s'.vg.cf = some F.cf ∧ s'.vg.zf = some (s.vg.gpr .rcx + 1 == 0) ∧
      s'.vg.of = some (addOverflow (s.vg.gpr .rcx) 1 (s.vg.gpr .rcx + 1)) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp d) F.w ∧ s'.vg.gpr .rbx = 0 ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  intro F
  sqrx_block [Rind.X86_64.Sqrx8x.inner, hrbp, hrdx, hst, hld, hcf, hof, hA]

end rind.x86_64.sqrx8x
