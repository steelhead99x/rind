import Rind.X86_64.Mulx4xAsm
import Rind.X86_64.Mul4xProof

/-! # bn_mulx4x_mont's prologue, stack walk, and setup

The pushes, then `rsp` lowered a page at a time to `fp`, the frame `8k + 120` to `8k + 247` bytes below the
stack pointer, 128-byte aligned, and the frame's slots stored. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mulx4x

theorem shl3_32 (k : Nat) (hk : k < 2 ^ 29) :
    (((BitVec.ofNat 64 k).setWidth 32) <<< 3).setWidth 64 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem signExtend_m128 : (-128 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18446744073709551488 := by decide

theorem and_mask7 (x : BitVec 64) : x &&& BitVec.ofNat 64 18446744073709551488 = (x >>> 7) <<< 7 := by
  rw [BitVec.shiftLeft_ushiftRight]; rfl

/-- The frame: `8k + 120` bytes below the stack pointer, aligned down to 128. -/
def fpOf (sp0 : Addr) (k : Nat) : Addr :=
  (sp0 - BitVec.ofNat 64 48 + (0 - BitVec.ofNat 64 (8 * k)) + BitVec.ofNat 64 18446744073709551544) &&&
    BitVec.ofNat 64 18446744073709551488

theorem fpOf_toNat (sp0 : Addr) (k : Nat) (hk : k < 2 ^ 29) (h : 8 * k + 120 ≤ sp0.toNat) :
    (fpOf sp0 k).toNat = (sp0.toNat - 8 * k - 120) / 128 * 128 := by
  have e : sp0 - BitVec.ofNat 64 48 + (0 - BitVec.ofNat 64 (8 * k)) + BitVec.ofNat 64 18446744073709551544 =
      sp0 - (BitVec.ofNat 64 (8 * k) + 120#64) := by
    generalize BitVec.ofNat 64 (8 * k) = x; bv_omega
  have hx : (BitVec.ofNat 64 (8 * k)).toNat = 8 * k := by rw [BitVec.toNat_ofNat]; omega
  unfold fpOf
  rw [e, and_mask7, toNat_shr_shl]
  congr 2
  rw [BitVec.toNat_sub, BitVec.toNat_add, hx]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The prologue's instructions up to the stack move: the pushes, `n0`, the frame, and the pages above it. -/
def prologueA : List Ins :=
  [.vg (.mov .rax (.reg .rsp)),
   .push .rbx,
   .push .rbp,
   .push .r12,
   .push .r13,
   .push .r14,
   .push .r15,
   .vg (.shift32 .shl .r9 3),
   .vg (.alu .xor .r10 (.reg .r10)),
   .vg (.alu .sub .r10 (.reg .r9)),
   .vg (.mov .r8 (.mem (Rind.X86_64.Mul4x.m .r8 0))),
   .lea .rbp (Rind.X86_64.Mul4x.mx .rsp .r10 1 (-72)),
   .vg (.alu .and .rbp (.imm (-128))),
   .vg (.mov .r11 (.reg .rsp)),
   .vg (.alu .sub .r11 (.reg .rbp)),
   .vg (.alu .and .r11 (.imm (-4096)))]

/-- The rest, which moves `rsp` and probes it. -/
def prologueB : List Ins :=
  [.leaRsp (Rind.X86_64.Mul4x.mx .r11 .rbp 1 0),
   .vg (.mov .r10 (.mem (Rind.X86_64.Mul4x.m .rsp 0))),
   .vg (.alu .cmp .rsp (.reg .rbp))]

theorem prologue_split : Rind.X86_64.Mulx4x.prologue = prologueA ++ prologueB := rfl

def prologueATrace (sp0 n0p : Addr) : List Leak :=
  [.addr (sp0 - BitVec.ofNat 64 8), .addr (sp0 - BitVec.ofNat 64 16), .addr (sp0 - BitVec.ofNat 64 24),
   .addr (sp0 - BitVec.ofNat 64 32), .addr (sp0 - BitVec.ofNat 64 40), .addr (sp0 - BitVec.ofNat 64 48),
   .addr n0p]

set_option hygiene false in
/-- Pushes' stack moves and stores, and the read of `n0`. -/
macro "xhead_disch" : tactic => `(tactic| no_recover first
  | decide
  | (simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem, gpr_setReg,
      wr_setReg, wr_arithFlags, gpr_arithFlags, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, reduceCtorEq,
      List.cons_ne_nil]; done)
  | (try simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem, gpr_setReg,
      wr_setReg, wr_arithFlags, gpr_arithFlags, rd_setWr, rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags,
      wr_setFlags, reduceCtorEq, ↓reduceIte]) <;>
     first
      | (refine inR List.mem_cons_self ?_; simp only; bv_omega)
      | (refine inR (List.mem_append_left _ rN0) ?_; simp only; bv_omega)
      | (unfold Apart; constructor <;> bv_omega)
      | bv_omega)

/-- Runs the prologue's instructions but `moveSp`. -/
syntax "xhead_run" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| xhead_run) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := xhead_disch) only [prologueA, hrsp, hr9, hr8, hwr, hn0,
      execAcc_cons, execAcc_nil, store64_of, load64_of, readW_writeW_sep, Rind.X86_64.exec, Rind.X86_64.addrs,
      VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, execAlu, execShift32, readSrc, readSrc32, VG.X86_64.State.setReg32,
      shl3_32 k hk, Option.map_some, Option.bind_some, State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit,
      Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow, sub_sub_ofNat, sub_sub_8, sub8_sub8,
      BitVec.xor_self, mul_ofNat_one, ofNat_zero, add_zero', signExtend_m128, signExtend_m4096, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.reduceLeDiff, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags,
      wr_setFlags, gpr_setWr, mem_setWr, rd_setWr, wr_setWr, gpr_setMem, mem_setMem, rd_setMem, wr_setMem,
      List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte, and_self, List.map_nil, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append])

set_option maxHeartbeats 4000000 in
theorem prologueA_ok (s : S) (k : Nat) (sp0 n0p n0' : Addr) (rest : List Region)
    (hk : k < 2 ^ 29) (hlo : s.lo.toNat + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = sp0) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k) (hr8 : s.vg.gpr .r8 = n0p)
    (hwr : s.vg.wr = ⟨sp0, 8⟩ :: rest) (rN0 : ⟨n0p, 8⟩ ∈ s.vg.rd) (hn0p : n0p.toNat + 8 ≤ 2 ^ 64)
    (sepN0 : n0p.toNat + 8 ≤ sp0.toNat - 48 ∨ sp0.toNat + 8 ≤ n0p.toNat)
    (hn0 : s.vg.mem.readW n0p 64 = n0') :
    ∃ s', execBlock I prologueA s = some (s', prologueATrace sp0 n0p) ∧
      s'.vg.gpr .rsp = sp0 - BitVec.ofNat 64 48 ∧ s'.vg.gpr .rax = sp0 ∧ s'.vg.gpr .r8 = n0' ∧
      s'.vg.gpr .r9 = BitVec.ofNat 64 (8 * k) ∧ s'.vg.gpr .rbp = fpOf sp0 k ∧
      s'.vg.gpr .r11 = pagesOf sp0 (fpOf sp0 k) ∧
      s'.vg.wr = ⟨sp0 - BitVec.ofNat 64 48, 56⟩ :: rest ∧
      s'.vg.mem = pushes s.vg.mem sp0 s.vg.gpr ∧
      (∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → s'.vg.gpr r = s.vg.gpr r) ∧ others s'.vg = others s.vg ∧
      s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo := by
  apply ex_of_eq
  · rw [execBlock_acc]
    xhead_run
    iterate 6 (rw [moveSp_down]; xhead_run; all_goals (first | xhead_disch | skip))
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setWr, gpr_setMem, gpr_arithFlags, gpr_setFlags, wr_setReg, wr_setWr, wr_setMem,
      wr_arithFlags, wr_setFlags, mem_setReg, mem_setWr, mem_setMem, mem_arithFlags, mem_setFlags, others_setReg,
      others_setWr, others_setMem, others_arithFlags, others_setFlags, reduceCtorEq, ↓reduceIte, hrsp]
    repeat' apply And.intro
    all_goals first
      | trivial
      | rfl
      | (simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]; bv_omega)
      | (intro r hr
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
         simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte])

set_option hygiene false in
/-- Stack moves, and probes of the claimed stack. -/
macro "xwalk_disch" : tactic => `(tactic| no_recover first
  | decide
  | (simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem, gpr_setReg,
      wr_setReg, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, List.cons_ne_nil]; done)
  | (try simp only [hwr, hrsp, List.headD_cons, List.tail_cons, wr_setWr, gpr_setWr, wr_setMem, gpr_setMem,
      gpr_setReg, wr_setReg, rd_setReg, rd_setWr, reduceCtorEq, ↓reduceIte]) <;>
     first
      | (refine inR (List.mem_append_right _ List.mem_cons_self) ?_; simp only; bv_omega)
      | bv_omega)

/-- Runs a stack walk's instructions but `moveSp`. -/
syntax "xwalk_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| xwalk_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 1000000 }) (disch := xwalk_disch) only [$xs,*, hrsp, hwr,
      execAcc_cons, execAcc_nil, load64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, readSrc, Option.map_some, Option.bind_some, State.ea, Rind.X86_64.Mul4x.m,
      Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow, mul_ofNat_one,
      ofNat_zero, add_zero', Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setWr, mem_setWr, rd_setWr,
      wr_setWr, List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append])

set_option maxHeartbeats 2000000 in
theorem prologueB_ok (s : S) (q fp P : Addr) (L : Nat) (rest : List Region)
    (hrsp : s.vg.gpr .rsp = q) (hrbp : s.vg.gpr .rbp = fp) (hr11 : s.vg.gpr .r11 = P)
    (hwr : s.vg.wr = ⟨q, L⟩ :: rest) (hL : 8 ≤ L) (hle : fp.toNat + P.toNat ≤ q.toNat)
    (hlo : s.lo.toNat ≤ fp.toNat) :
    ∃ s', execBlock I prologueB s = some (s', [.addr (P + fp)]) ∧
      s'.vg.gpr .rsp = P + fp ∧ s'.vg.gpr .rbp = fp ∧ s'.vg.wr = ⟨P + fp, L + (q.toNat - (P + fp).toNat)⟩ :: rest ∧
      s'.vg.cf = some (decide ((P + fp).toNat < fp.toNat)) ∧ s'.vg.zf = some (P + fp - fp == 0) ∧
      FrameS s s' [.rsp, .r10] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    xwalk_run [prologueB, hrbp, hr11]
    rw [moveSp_down]
    xwalk_run [prologueB, hrbp, hr11]
    all_goals (first | xwalk_disch | skip)
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setWr, gpr_arithFlags, wr_setReg, wr_setWr, wr_arithFlags, hrsp, hwr,
      List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte, cf_arithFlags, zf_arithFlags]
    repeat' apply And.intro
    all_goals try first
      | trivial
      | rfl
    · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, gpr_setWr, hr.1, hr.2, ↓reduceIte]

set_option maxHeartbeats 2000000 in
theorem walk_ok (s : S) (fp X : Addr) (L : Nat) (rest : List Region)
    (hrsp : s.vg.gpr .rsp = fp + (X + BitVec.ofNat 64 4096)) (hrbp : s.vg.gpr .rbp = fp)
    (hwr : s.vg.wr = ⟨fp + (X + BitVec.ofNat 64 4096), L⟩ :: rest)
    (hno : fp.toNat + X.toNat + 4096 < 2 ^ 64) (hlo : s.lo.toNat ≤ fp.toNat) :
    ∃ s', execBlock I Rind.X86_64.Mulx4x.walk s = some (s', [.addr (fp + X)]) ∧
      s'.vg.gpr .rsp = fp + X ∧ s'.vg.gpr .rbp = fp ∧
      s'.vg.wr = ⟨fp + X, L + ((fp + (X + BitVec.ofNat 64 4096)).toNat - (fp + X).toNat)⟩ :: rest ∧
      s'.vg.cf = some (decide ((fp + X).toNat < fp.toNat)) ∧ s'.vg.zf = some (fp + X - fp == 0) ∧
      FrameS s s' [.rsp, .r10] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    xwalk_run [Rind.X86_64.Mulx4x.walk, hrbp, walk_addr]
    rw [moveSp_down]
    xwalk_run [Rind.X86_64.Mulx4x.walk, hrbp, walk_addr]
    all_goals (first | xwalk_disch | skip)
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

/-- The walk down from `m` pages above `fp`, before step `i`. -/
structure WalkInv (s₀ s : S) (fp sp0 : Addr) (rest : List Region) (m i : Nat) : Prop where
  rsp : s.vg.gpr .rsp = fp + BitVec.ofNat 64 (4096 * (m - i))
  rbp : s.vg.gpr .rbp = fp
  wr : s.vg.wr = ⟨fp + BitVec.ofNat 64 (4096 * (m - i)), sp0.toNat + 8 - (fp + BitVec.ofNat 64 (4096 * (m - i))).toNat⟩ ::
    rest
  frame : FrameS s₀ s [.rsp, .r10]

/-- The walk's loop body: its alignment, then `walk`. -/
abbrev walkBody : Prog I := .seq (.block [.align 16]) (.block Rind.X86_64.Mulx4x.walk)

theorem walk_loop (s₀ : S) (fp sp0 : Addr) (rest : List Region) (m : Nat) (hm : 1 ≤ m)
    (hno : fp.toNat + 4096 * m + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hlo : s₀.lo.toNat ≤ fp.toNat)
    (hI : WalkInv s₀ s₀ fp sp0 rest m 0) :
    ∃ s', Exec I (.loop walkBody Rind.X86_64.Cond.a) s₀
      (loopTrace (fun i => [.addr (fp + BitVec.ofNat 64 (4096 * (m - i - 1)))]) 1 0 (m - 1)) s' ∧
      WalkInv s₀ s' fp sp0 rest m m := by
  have step : ∀ i s, WalkInv s₀ s fp sp0 rest m i → i < m →
      ∃ s', Exec I walkBody s [.addr (fp + BitVec.ofNat 64 (4096 * (m - i - 1)))] s' ∧
        I.eval Rind.X86_64.Cond.a s' = some (decide (i + 1 < m)) ∧ WalkInv s₀ s' fp sp0 rest m (i + 1) := by
    intro i s hI hi
    have e : fp + BitVec.ofNat 64 (4096 * (m - i)) =
        fp + (BitVec.ofNat 64 (4096 * (m - i - 1)) + BitVec.ofNat 64 4096) := by
      rw [BitVec.ofNat_add_ofNat]; congr 2; omega
    have hX : (BitVec.ofNat 64 (4096 * (m - i - 1))).toNat = 4096 * (m - i - 1) := by simp; omega
    obtain ⟨s', hx, o_sp, obp, owr, ocf, ozf, oF⟩ :=
      walk_ok s fp (BitVec.ofNat 64 (4096 * (m - i - 1))) _ rest (hI.rsp.trans e) hI.rbp (e ▸ hI.wr)
        (by rw [hX]; omega) (by rw [hI.frame.lo]; exact hlo)
    have hY : (fp + BitVec.ofNat 64 (4096 * (m - i - 1))).toNat = fp.toNat + 4096 * (m - i - 1) := by
      rw [BitVec.toNat_add, hX]; omega
    have hY' : (fp + BitVec.ofNat 64 (4096 * (m - i))).toNat = fp.toNat + 4096 * (m - i) := by
      rw [BitVec.toNat_add]; simp; omega
    have hs := Exec.seq (Exec.block (M := I) (is := [.align 16]) (s := s) (s' := s) (t := []) rfl) (Exec.block hx)
    rw [List.nil_append] at hs
    refine ⟨s', hs, ?_, ?_, obp, ?_, hI.frame.trans oF⟩
    · simp only [Rind.X86_64.isa, Rind.X86_64.eval, ocf, ozf, Option.bind_some, Option.map_some]
      have h1 : decide ((fp + BitVec.ofNat 64 (4096 * (m - i - 1))).toNat < fp.toNat) = false := by
        rw [hY]; simp
      have h2 : (fp + BitVec.ofNat 64 (4096 * (m - i - 1)) - fp == 0) = decide (m - i - 1 = 0) := by
        rw [show fp + BitVec.ofNat 64 (4096 * (m - i - 1)) - fp = BitVec.ofNat 64 (4096 * (m - i - 1)) by bv_omega]
        by_cases h : m - i - 1 = 0
        · simp [h]
        · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
          intro h'; have := congrArg BitVec.toNat h'; rw [hX] at this; simp at this; omega
      have h3 : (m - i - 1 = 0) ↔ ¬(i + 1 < m) := by omega
      rw [h1, h2]; simp only [h3, Bool.not_false, Bool.true_and, decide_not, Bool.not_not]
    · rw [o_sp]; rfl
    · rw [show m - (i + 1) = m - i - 1 by omega, owr, ← e, hY, hY']
      simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]
      omega
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := walkBody) (c := Rind.X86_64.Cond.a)
    (fun i s => WalkInv s₀ s fp sp0 rest m i) (fun i => i < m) (fun i => decide (i + 1 < m))
    (fun i => [.addr (fp + BitVec.ofNat 64 (4096 * (m - i - 1)))]) 1 step (m - 1) 0 s₀ hI
    (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 0 + 1 * (m - 1 + 1) = m by omega] at hI'
  exact ⟨s', hx, hI'⟩

/-- The walk's trace, from `m` pages above `fp`. -/
def walkTrace (fp : Addr) (m : Nat) : List Leak :=
  if m = 0 then [.branch false]
  else .branch true :: loopTrace (fun i => [.addr (fp + BitVec.ofNat 64 (4096 * (m - i - 1)))]) 1 0 (m - 1)

set_option maxHeartbeats 1000000 in
theorem head_ok (s : S) (k : Nat) (sp0 n0p n0' : Addr) (rest : List Region)
    (hk : k < 2 ^ 29) (hlo : s.lo.toNat + 8 * k + 248 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = sp0) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k) (hr8 : s.vg.gpr .r8 = n0p)
    (hwr : s.vg.wr = ⟨sp0, 8⟩ :: rest) (rN0 : ⟨n0p, 8⟩ ∈ s.vg.rd) (hn0p : n0p.toNat + 8 ≤ 2 ^ 64)
    (sepN0 : n0p.toNat + 8 ≤ sp0.toNat - 48 ∨ sp0.toNat + 8 ≤ n0p.toNat)
    (hn0 : s.vg.mem.readW n0p 64 = n0') :
    ∃ s₁ s', Exec I (.block Rind.X86_64.Mulx4x.prologue) s
        (prologueATrace sp0 n0p ++ [.addr (pagesOf sp0 (fpOf sp0 k) + fpOf sp0 k)]) s₁ ∧
      Exec I (.ite Rind.X86_64.Cond.a (.loop walkBody Rind.X86_64.Cond.a) (.block [])) s₁
        (walkTrace (fpOf sp0 k) ((pagesOf sp0 (fpOf sp0 k)).toNat / 4096)) s' ∧
      s'.vg.gpr .rsp = fpOf sp0 k ∧ s'.vg.gpr .rax = sp0 ∧ s'.vg.gpr .r8 = n0' ∧
      s'.vg.gpr .r9 = BitVec.ofNat 64 (8 * k) ∧
      s'.vg.wr = ⟨fpOf sp0 k, sp0.toNat + 8 - (fpOf sp0 k).toNat⟩ :: rest ∧
      s'.vg.mem = pushes s.vg.mem sp0 s.vg.gpr ∧
      (∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → s'.vg.gpr r = s.vg.gpr r) ∧
      others s'.vg = others s.vg ∧ s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo := by
  obtain ⟨s₁, hxA, a_sp, a_ax, a8, a9, abp, a11, awr, amem, ag, aoth, amx, alo⟩ :=
    prologueA_ok s k sp0 n0p n0' rest hk (by omega) hsp hrsp hr9 hr8 hwr rN0 hn0p sepN0 hn0
  have hfp := fpOf_toNat sp0 k hk (by omega)
  generalize fpOf sp0 k = fp at hfp abp a11 ⊢
  have t1 := Nat.div_add_mod (sp0.toNat - 8 * k - 120) 128
  have t2 := Nat.mod_lt (sp0.toNat - 8 * k - 120) (show 128 > 0 by norm_num)
  have t3 : fp.toNat + 8 * k + 120 ≤ sp0.toNat ∧ sp0.toNat ≤ fp.toNat + 8 * k + 247 := by
    rw [hfp]; constructor <;> omega
  clear t1 t2
  have hP := pagesOf_toNat sp0 fp (by omega)
  have hq : (sp0 - BitVec.ofNat 64 48).toNat = sp0.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  generalize pagesOf sp0 fp = P at hP a11 ⊢
  have p1 := Nat.div_add_mod (sp0.toNat - 48 - fp.toNat) 4096
  have p2 := Nat.mod_lt (sp0.toNat - 48 - fp.toNat) (show 4096 > 0 by norm_num)
  have p3 : P.toNat ≤ sp0.toNat - 48 - fp.toNat ∧ P.toNat % 4096 = 0 := by rw [hP]; omega
  clear p1 p2
  have hTP : (P + fp).toNat = fp.toNat + P.toNat := by rw [BitVec.toNat_add]; omega
  obtain ⟨s₂, hxB, b_sp, bbp, bwr, bcf, bzf, bF⟩ :=
    prologueB_ok s₁ (sp0 - BitVec.ofNat 64 48) fp P 56 rest a_sp abp a11 awr (by omega) (by omega)
      (by rw [alo]; omega)
  have hxP : execBlock I Rind.X86_64.Mulx4x.prologue s = some (s₂, prologueATrace sp0 n0p ++ [.addr (P + fp)]) := by
    rw [prologue_split, execBlock_append, hxA]
    simp only [Option.bind_some, hxB, Option.map_some]
  have hPf : P + fp = fp + P := BitVec.add_comm _ _
  set m := P.toNat / 4096 with hm
  have hPm : P = BitVec.ofNat 64 (4096 * m) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  have hev : I.eval Rind.X86_64.Cond.a s₂ = some (!decide (m = 0)) := by
    simp only [Rind.X86_64.isa, Rind.X86_64.eval, bcf, bzf, Option.bind_some, Option.map_some]
    have h1 : decide ((P + fp).toNat < fp.toNat) = false := by rw [hTP]; simp
    have h2 : (P + fp - fp == 0) = decide (m = 0) := by
      rw [show P + fp - fp = P by bv_omega]
      by_cases h : m = 0
      · have hP0 : P = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
        simp only [h, hP0, decide_true, beq_self_eq_true]
      · have hP0 : P ≠ 0 := fun h' => by rw [h', show (0 : BitVec 64).toNat = 0 from rfl] at hm; exact h hm
        simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, hP0, not_false_eq_true]
    rw [h1, h2, Bool.not_false, Bool.true_and]
  have hwalk : ∃ s₃, Exec I (.ite Rind.X86_64.Cond.a (.loop walkBody Rind.X86_64.Cond.a) (.block [])) s₂
      (walkTrace fp m) s₃ ∧ s₃.vg.gpr .rsp = fp ∧ s₃.vg.wr = ⟨fp, sp0.toNat + 8 - fp.toNat⟩ :: rest ∧
      FrameS s₂ s₃ [.rsp, .r10] := by
    by_cases h0 : m = 0
    · have hP0 : P = 0 := by rw [hPm, h0]; rfl
      refine ⟨s₂, ?_, by rw [b_sp, hP0]; exact BitVec.zero_add _, ?_, FrameS.refl _ _⟩
      · simp only [walkTrace, h0, ↓reduceIte]
        exact Exec.iteF (by rw [hev, h0]; rfl) (Exec.block rfl)
      · have hP0n : P.toNat = 0 := by omega
        rw [bwr, hTP, hq, hP0n, hP0]
        simp only [List.cons.injEq, Region.mk.injEq, and_true]
        exact ⟨BitVec.zero_add _, by omega⟩
    · have hI : WalkInv s₂ s₂ fp sp0 rest m 0 := by
        refine ⟨by rw [b_sp, hPf, hPm]; rfl, bbp, ?_, FrameS.refl _ _⟩
        simp only [Nat.sub_zero]
        rw [bwr, ← hPm, ← hPf, hTP, hq]
        simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]
        omega
      obtain ⟨s₃, hx3, hI3⟩ := walk_loop s₂ fp sp0 rest m (by omega) (by omega) hsp
        (by rw [bF.lo, alo]; omega) hI
      refine ⟨s₃, ?_, ?_, ?_, hI3.frame⟩
      · simp only [walkTrace, h0, ↓reduceIte]
        exact Exec.iteT (by rw [hev]; simp [h0]) hx3
      · rw [hI3.rsp, Nat.sub_self, Nat.mul_zero]; exact BitVec.add_zero _
      · rw [hI3.wr, Nat.sub_self, Nat.mul_zero]; simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  obtain ⟨s₃, hx3, c_sp, cwr, cF⟩ := hwalk
  have F := bF.trans cF
  refine ⟨s₂, s₃, Exec.block hxP, hx3, c_sp, ?_, ?_, ?_, cwr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [F.gpr _ (by decide), a_ax]
  · rw [F.gpr _ (by decide), a8]
  · rw [F.gpr _ (by decide), a9]
  · rw [F.mem, amem]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [F.gpr r (by simp [hr.1, hr.2.2.2.2.2.1]),
      ag r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2])]
  · rw [F.others, aoth]
  · rw [F.mxcsr, amx]
  · rw [F.lo, alo]

/-! ## The frame's slots -/

theorem signExtend_one' : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem mul8_div8 (k : Nat) : 8 * k / 8 = k := by omega

def setupTrace (fp : Addr) : List Leak :=
  [.addr fp, .addr (wa fp 2), .addr (wa fp 3), .addr (wa fp 4), .addr (wa fp 5), .addr (wa fp 6)]

set_option maxHeartbeats 4000000 in
theorem setup_ok (s : S) (k : Nat) (ap bp np fp rp sp0 n0' : Addr) (hk8 : 8 ≤ k) (ar : Arr s k ap bp np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrdx : s.vg.gpr .rdx = bp) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k))
    (hr8 : s.vg.gpr .r8 = n0') (hrdi : s.vg.gpr .rdi = rp) (hrax : s.vg.gpr .rax = sp0) :
    ∃ s', execBlock I Rind.X86_64.Mulx4x.setup s = some (s', setupTrace fp) ∧
      s'.vg.mem = (((((s.vg.mem.writeW fp (BitVec.ofNat 64 (8 * k))).writeW (wa fp 2)
        (wa bp k)).writeW (wa fp 3) n0').writeW (wa fp 4) rp).writeW (wa fp 5) sp0).writeW
        (wa fp 6) (BitVec.ofNat 64 (8 * k / 32) - 1) ∧
      Frame s s' [.r9, .r10] := by
  obtain ⟨hk, hap, hbp, hnp, hfp, sepA, sepB, sepN, rA, rB, rN, LF, hLF, rF⟩ := ar
  have h8k : 8 * k < 2 ^ 64 := by omega
  mulx_block [Rind.X86_64.Mulx4x.setup, hrsp, hrdx, hr9, hr8, hrdi, hrax, execShift, ofNat_shr (8 * k) 5 h8k,
    signExtend_one', mul_ofNat_one, Nat.reduceLeDiff, and_self, Nat.reducePow, mul8_div8]

end rind.x86_64.mulx4x
