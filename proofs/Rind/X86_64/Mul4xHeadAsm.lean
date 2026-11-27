import Rind.X86_64.Mul4xTailAsm

/-! # bn_mul4x_mont's prologue

The pushes, the scratch space's address `tp`, and the walk down to it a page at a time. -/

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mul4x

/-- The state with writable regions `w`. -/
def setWr (g : VG.X86_64.State) (w : List Region) : VG.X86_64.State := { g with wr := w }

section
variable (g : VG.X86_64.State) (w : List Region)
@[simp] theorem gpr_setWr : (setWr g w).gpr = g.gpr := rfl
@[simp] theorem mem_setWr : (setWr g w).mem = g.mem := rfl
@[simp] theorem rd_setWr : (setWr g w).rd = g.rd := rfl
@[simp] theorem wr_setWr : (setWr g w).wr = w := rfl
@[simp] theorem cf_setWr : (setWr g w).cf = g.cf := rfl
@[simp] theorem zf_setWr : (setWr g w).zf = g.zf := rfl
@[simp] theorem xmm_setWr : (setWr g w).xmm = g.xmm := rfl
@[simp] theorem mxcsr_setWr : (setWr g w).mxcsr = g.mxcsr := rfl
@[simp] theorem others_setWr : others (setWr g w) = others g := rfl
end

/-- `lea rsp` or a push lowering the stack pointer, no lower than `lo`. -/
theorem moveSp_down (s : S) (v : Addr) (hb : (s.vg.wr.headD ⟨0, 0⟩).base = s.vg.gpr .rsp)
    (hne : s.vg.wr ≠ []) (h1 : s.lo.toNat ≤ v.toNat) (h2 : v.toNat ≤ (s.vg.gpr .rsp).toNat) :
    Rind.X86_64.moveSp s v = some { s with vg := (setWr (s.vg.setReg .rsp v)
      (⟨v, (s.vg.wr.headD ⟨0, 0⟩).len + ((s.vg.gpr .rsp).toNat - v.toNat)⟩ :: s.vg.wr.tail)) } := by
  obtain ⟨r, rs, hw⟩ : ∃ r rs, s.vg.wr = r :: rs := by
    cases h : s.vg.wr with
    | nil => exact absurd h hne
    | cons r rs => exact ⟨r, rs, rfl⟩
  rw [hw] at hb
  have hc : Rind.X86_64.claimed s.vg = some r.len := by
    simp only [Rind.X86_64.claimed, hw]; simp only [List.headD_cons] at hb; simp [hb]
  simp only [Rind.X86_64.moveSp, hc, Option.bind_some, hw, List.headD_cons, List.tail_cons]
  rw [if_pos ⟨h1, h2⟩]
  rfl

theorem sub_sub_ofNat (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem sub_sub_8 (x : BitVec 64) (a : Nat) : x - BitVec.ofNat 64 a - 8 = x - BitVec.ofNat 64 (a + 8) :=
  sub_sub_ofNat x a 8

theorem sub8_sub8 (x : BitVec 64) : x - 8 - 8 = x - BitVec.ofNat 64 16 := sub_sub_ofNat x 8 8

theorem zero_sub_zero_sub (x : BitVec 64) : 0 - (0 - x) = x := by bv_decide

theorem setWidth_ofNat32 (k : Nat) (h : k < 2 ^ 32) :
    ((BitVec.ofNat 64 k).setWidth 32).setWidth 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem signExtend_m1024 : (-1024 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18446744073709550592 := by decide
theorem signExtend_m4096 : (-4096 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18446744073709547520 := by decide

/-- The scratch space: `8k + 32` bytes below the pushes, aligned down to 1024. -/
def tpOf (sp0 : Addr) (k : Nat) : Addr :=
  (sp0 - BitVec.ofNat 64 48 + (0 - BitVec.ofNat 64 k) * 8#64 + BitVec.ofNat 64 18446744073709551584) &&&
    BitVec.ofNat 64 18446744073709550592

/-- How far below the pushes `lea rsp` first moves, in whole pages. -/
def pagesOf (sp0 tp : Addr) : Addr := (sp0 - BitVec.ofNat 64 48 - tp) &&& BitVec.ofNat 64 18446744073709547520

/-- The prologue's first fifteen instructions, which push and compute `tp` and the pages above it. -/
def prologueA : List Ins :=
  [.vg (.mov32 .r9 (.reg .r9)),
   .vg (.mov .rax (.reg .rsp)),
   .push .rbx,
   .push .rbp,
   .push .r12,
   .push .r13,
   .push .r14,
   .push .r15,
   .neg .r9,
   .vg (.mov .r11 (.reg .rsp)),
   .lea .r10 (mx .rsp .r9 8 (-32)),
   .neg .r9,
   .vg (.alu .and .r10 (.imm (-1024))),
   .vg (.alu .sub .r11 (.reg .r10)),
   .vg (.alu .and .r11 (.imm (-4096)))]

/-- The rest, which moves `rsp` and probes it. -/
def prologueB : List Ins :=
  [.leaRsp (mx .r10 .r11 1 0),
   .vg (.mov .r11 (.mem (m .rsp 0))),
   .vg (.alu .cmp .rsp (.reg .r10))]

theorem prologue_split : prologue = prologueA ++ prologueB := rfl

def prologueATrace (sp0 : Addr) : List Leak :=
  [.addr (sp0 - BitVec.ofNat 64 8), .addr (sp0 - BitVec.ofNat 64 16), .addr (sp0 - BitVec.ofNat 64 24),
   .addr (sp0 - BitVec.ofNat 64 32), .addr (sp0 - BitVec.ofNat 64 40), .addr (sp0 - BitVec.ofNat 64 48)]

set_option hygiene false in
/-- Pushes' stack moves and stores. -/
macro "head_disch" : tactic => `(tactic| no_recover first
  | decide
  | (simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem, gpr_setReg,
      wr_setReg, wr_arithFlags, gpr_arithFlags, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, reduceCtorEq,
      List.cons_ne_nil]; done)
  | (try simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem, gpr_setReg,
      wr_setReg, wr_arithFlags, gpr_arithFlags, reduceCtorEq, ↓reduceIte]) <;>
     first
      | (refine inR List.mem_cons_self ?_; simp only; bv_omega)
      | bv_omega)

/-- Runs the prologue's instructions but `moveSp`. -/
syntax "head_run" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| head_run) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := head_disch) only [prologueA, hrsp, hr9, hwr,
      execAcc_cons, execAcc_nil, store64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, readSrc, readSrc32, VG.X86_64.State.setReg32, setWidth_ofNat32 k hk,
      Option.map_some, Option.bind_some, State.ea, m, mx, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat,
      Int.reducePow, sub_sub_ofNat, sub_sub_8, sub8_sub8, zero_sub_zero_sub, signExtend_m1024, signExtend_m4096,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setWr, mem_setWr, rd_setWr, wr_setWr,
      gpr_setMem, mem_setMem, rd_setMem, wr_setMem, List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte,
      List.map_nil, List.map_cons, List.append_nil, List.nil_append, List.cons_append])

set_option maxHeartbeats 4000000 in
theorem prologueA_ok (s : S) (k : Nat) (sp0 : Addr) (rest : List Region)
    (hk : k < 2 ^ 32) (hlo : s.lo.toNat + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = sp0) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hwr : s.vg.wr = ⟨sp0, 8⟩ :: rest) :
    ∃ s', execBlock I prologueA s = some (s', prologueATrace sp0) ∧
      s'.vg.gpr .rsp = sp0 - BitVec.ofNat 64 48 ∧ s'.vg.gpr .rax = sp0 ∧ s'.vg.gpr .r9 = BitVec.ofNat 64 k ∧
      s'.vg.gpr .r10 = tpOf sp0 k ∧ s'.vg.gpr .r11 = pagesOf sp0 (tpOf sp0 k) ∧
      s'.vg.wr = ⟨sp0 - BitVec.ofNat 64 48, 56⟩ :: rest ∧
      s'.vg.mem = (((((s.vg.mem.writeW (sp0 - BitVec.ofNat 64 8) (s.vg.gpr .rbx)).writeW (sp0 - BitVec.ofNat 64 16)
        (s.vg.gpr .rbp)).writeW (sp0 - BitVec.ofNat 64 24) (s.vg.gpr .r12)).writeW (sp0 - BitVec.ofNat 64 32)
        (s.vg.gpr .r13)).writeW (sp0 - BitVec.ofNat 64 40) (s.vg.gpr .r14)).writeW (sp0 - BitVec.ofNat 64 48)
        (s.vg.gpr .r15) ∧
      (∀ r, r ∉ [Reg.rsp, .rax, .r9, .r10, .r11] → s'.vg.gpr r = s.vg.gpr r) ∧ others s'.vg = others s.vg ∧
      s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo := by
  apply ex_of_eq
  · rw [execBlock_acc]
    head_run
    iterate 6 (rw [moveSp_down]; head_run; all_goals (first | head_disch | skip))
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setWr, gpr_setMem, gpr_arithFlags, wr_setReg, wr_setWr, wr_setMem, wr_arithFlags,
      mem_setReg, mem_setWr, mem_setMem, mem_arithFlags, others_setReg, others_setWr, others_setMem,
      others_arithFlags, reduceCtorEq, ↓reduceIte, hrsp]
    repeat' apply And.intro
    all_goals first
      | trivial
      | rfl
      | (simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]; bv_omega)
      | (intro r hr
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h1, h2, h3, h4, h5⟩ := hr
         simp only [h1, h2, h3, h4, h5, ↓reduceIte])

set_option hygiene false in
/-- Stack moves, and probes of the claimed stack. -/
macro "walk_disch" : tactic => `(tactic| no_recover first
  | decide
  | (simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem, gpr_setReg,
      wr_setReg, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, List.cons_ne_nil]; done)
  | (try simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem,
      gpr_setReg, wr_setReg, rd_setReg, rd_setWr, reduceCtorEq, ↓reduceIte]) <;>
     first
      | (refine inR (List.mem_append_right _ List.mem_cons_self) ?_; simp only; bv_omega)
      | bv_omega)

/-- Runs a stack walk's instructions but `moveSp`. -/
syntax "walk_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| walk_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 1000000 }) (disch := walk_disch) only [$xs,*, hrsp, hwr,
      execAcc_cons, execAcc_nil, load64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, readSrc, Option.map_some, Option.bind_some, State.ea, m, mx, ofInt_lit, Int.reduceNeg,
      Int.reduceMod, Int.reduceToNat, Int.reducePow, mul_ofNat_one, ofNat_zero, add_zero', Nat.reduceAdd,
      Nat.reduceSub, Nat.reducePow, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, gpr_setWr, mem_setWr, rd_setWr, wr_setWr, List.headD_cons, List.tail_cons,
      reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons, List.append_nil, List.nil_append, List.cons_append])

/-- What a stack move leaves unchanged: the general registers but `gs`, memory, and the rest but `wr`. -/
structure FrameS (s s' : S) (gs : List Reg) : Prop where
  gpr : ∀ r, r ∉ gs → s'.vg.gpr r = s.vg.gpr r
  mem : s'.vg.mem = s.vg.mem
  others : others s'.vg = others s.vg
  xmm : s'.vg.xmm = s.vg.xmm
  mxcsr : s'.vg.mxcsr = s.vg.mxcsr
  lo : s'.lo = s.lo

set_option maxHeartbeats 2000000 in
theorem prologueB_ok (s : S) (q tp P : Addr) (L : Nat) (rest : List Region)
    (hrsp : s.vg.gpr .rsp = q) (hr10 : s.vg.gpr .r10 = tp) (hr11 : s.vg.gpr .r11 = P)
    (hwr : s.vg.wr = ⟨q, L⟩ :: rest) (hL : 8 ≤ L) (hle : tp.toNat + P.toNat ≤ q.toNat)
    (hlo : s.lo.toNat ≤ tp.toNat) :
    ∃ s', execBlock I prologueB s = some (s', [.addr (tp + P)]) ∧
      s'.vg.gpr .rsp = tp + P ∧ s'.vg.gpr .r10 = tp ∧ s'.vg.wr = ⟨tp + P, L + (q.toNat - (tp + P).toNat)⟩ :: rest ∧
      s'.vg.cf = some (decide ((tp + P).toNat < tp.toNat)) ∧ s'.vg.zf = some (tp + P - tp == 0) ∧
      FrameS s s' [.rsp, .r11] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    walk_run [prologueB, hr10, hr11]
    rw [moveSp_down]
    walk_run [prologueB, hr10, hr11]
    all_goals (first | walk_disch | skip)
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setWr, gpr_arithFlags, wr_setReg, wr_setWr, wr_arithFlags, hrsp, hwr,
      List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte, cf_arithFlags, zf_arithFlags]
    repeat' apply And.intro
    all_goals first
      | trivial
      | rfl
      | skip
    · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, gpr_setWr, hr.1, hr.2, ↓reduceIte]

theorem walk_addr (tp X : Addr) : tp + (X + BitVec.ofNat 64 4096) + BitVec.ofNat 64 18446744073709547520 = tp + X := by
  bv_omega

set_option maxHeartbeats 2000000 in
theorem walk_ok (s : S) (tp X : Addr) (L : Nat) (rest : List Region)
    (hrsp : s.vg.gpr .rsp = tp + (X + BitVec.ofNat 64 4096)) (hr10 : s.vg.gpr .r10 = tp)
    (hwr : s.vg.wr = ⟨tp + (X + BitVec.ofNat 64 4096), L⟩ :: rest)
    (hno : tp.toNat + X.toNat + 4096 < 2 ^ 64) (hlo : s.lo.toNat ≤ tp.toNat) :
    ∃ s', execBlock I walk s = some (s', [.addr (tp + X)]) ∧
      s'.vg.gpr .rsp = tp + X ∧ s'.vg.gpr .r10 = tp ∧
      s'.vg.wr = ⟨tp + X, L + ((tp + (X + BitVec.ofNat 64 4096)).toNat - (tp + X).toNat)⟩ :: rest ∧
      s'.vg.cf = some (decide ((tp + X).toNat < tp.toNat)) ∧ s'.vg.zf = some (tp + X - tp == 0) ∧
      FrameS s s' [.rsp, .r11] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    walk_run [walk, hr10, walk_addr]
    rw [moveSp_down]
    walk_run [walk, hr10, walk_addr]
    all_goals (first | walk_disch | skip)
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setWr, gpr_arithFlags, wr_setReg, wr_setWr, wr_arithFlags, hrsp, hwr,
      List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte, cf_arithFlags, zf_arithFlags]
    repeat' apply And.intro
    all_goals first
      | trivial
      | rfl
      | skip
    · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, gpr_setWr, hr.1, hr.2, ↓reduceIte]

end rind.x86_64.mul4x
