import RindIsa.X86_64.Sqrx8xMont
import Rind.X86_64.Mulx4xHead

/-! # bn_sqrx8x_mont's prologue and stack walk

The pushes, then `rsp` lowered a page at a time to `wsp`, the frame of `2k + 8` words at least `16k + 112` bytes
below the stack pointer, nudged lower if `ap` would share its offset within a page, 64-byte aligned. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8xmont

theorem shl5 (k : Nat) : BitVec.ofNat 64 k <<< 5 = BitVec.ofNat 64 (32 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem signExtend_m64 : (-64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18446744073709551552 := by decide
theorem signExtend_4095 : (4095 : BitVec 32).signExtend 64 = 4095#64 := by decide
theorem signExtend_4032 : (4032 : BitVec 32).signExtend 64 = 4032#64 := by decide

/-- How far past a page boundary the frame's first guess, `16k + 112` bytes below the stack pointer, lies from
`ap`. -/
def offOf (sp0 ap : Addr) (k : Nat) : Addr := (sp0 - BitVec.ofNat 64 (16 * k + 112) - ap) &&& 4095#64

theorem neg_mul2 (k : Nat) : (0 - BitVec.ofNat 64 (8 * k)) * 2#64 = 0 - BitVec.ofNat 64 (16 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
  omega

theorem lin112 (x y : Addr) : x - 48#64 + (0 - y) + 18446744073709551552#64 = x - (y + 112#64) := by
  bv_omega

theorem add_zsub (a y : Addr) : a + (0 - y) = a - y := by bv_omega

theorem add_m64 (a : Addr) : a + 18446744073709551552#64 = a - 64#64 := by bv_omega

theorem linNear (x o y : Addr) : x - 48#64 - o + (0 - y) + 18446744073709551552#64 = x - (o + (y + 112#64)) := by
  simp only [add_zsub, add_m64, BitVec.sub_sub]
  refine congrArg (x - ·) ?_
  bv_omega

theorem off_eq (sp0 ap : Addr) (k : Nat) :
    (sp0 - 48#64 + (0 - BitVec.ofNat 64 (8 * k)) * 2#64 + 18446744073709551552#64 - ap &&& 4095#64) =
      offOf sp0 ap k := by
  unfold offOf; rw [neg_mul2, lin112, BitVec.ofNat_add_ofNat]

theorem offOf_lt (sp0 ap : Addr) (k : Nat) : (offOf sp0 ap k).toNat < 4096 := by
  unfold offOf; rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

set_option hygiene false in
/-- Pushes' stack moves and stores, and the read of `n0`. -/
macro "shead_disch" : tactic => `(tactic| no_recover first
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
syntax "shead_run" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| shead_run) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := shead_disch) only [Rind.X86_64.Sqrx8xMont.prologue, hrsp,
      hr9, hr8, hrsi, hwr, hn0, execAcc_cons, execAcc_nil, store64_of, load64_of, readW_writeW_sep, Rind.X86_64.exec,
      Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, execAlu, execShift, execShift32, readSrc,
      readSrc32, VG.X86_64.State.setReg32, setWidth_ofNat32 k (by omega), shl3_32 k hk, shl5 k, Option.map_some,
      Option.bind_some, State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit, Int.reduceNeg, Int.reduceMod,
      Int.reduceToNat, Int.reducePow, sub_sub_ofNat, sub_sub_8, sub8_sub8, mul_ofNat_one, ofNat_zero, add_zero',
      signExtend_m64, signExtend_4095, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow,
      Nat.reduceLeDiff, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags, rd_arithFlags,
      wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, gpr_setWr, mem_setWr, rd_setWr, wr_setWr,
      gpr_setMem, mem_setMem, rd_setMem, wr_setMem, List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte,
      and_self, List.map_nil, List.map_cons, List.append_nil, List.nil_append, List.cons_append])

set_option maxHeartbeats 4000000 in
theorem prologue_ok (s : S) (k : Nat) (sp0 ap n0p n0' : Addr) (rest : List Region)
    (hk : k < 2 ^ 29) (hlo : s.lo.toNat + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = sp0) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k) (hr8 : s.vg.gpr .r8 = n0p)
    (hrsi : s.vg.gpr .rsi = ap)
    (hwr : s.vg.wr = ⟨sp0, 8⟩ :: rest) (rN0 : ⟨n0p, 8⟩ ∈ s.vg.rd) (hn0p : n0p.toNat + 8 ≤ 2 ^ 64)
    (sepN0 : n0p.toNat + 8 ≤ sp0.toNat - 48 ∨ sp0.toNat + 8 ≤ n0p.toNat)
    (hn0 : s.vg.mem.readW n0p 64 = n0') :
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.prologue s = some (s', mulx4x.prologueATrace sp0 n0p) ∧
      s'.vg.gpr .rsp = sp0 - BitVec.ofNat 64 48 ∧ s'.vg.gpr .rax = sp0 ∧ s'.vg.gpr .r8 = n0' ∧
      s'.vg.gpr .r9 = 0 - BitVec.ofNat 64 (8 * k) ∧ s'.vg.gpr .r10 = BitVec.ofNat 64 (32 * k) ∧
      s'.vg.gpr .rbp = sp0 - BitVec.ofNat 64 48 ∧ s'.vg.gpr .r11 = offOf sp0 ap k ∧
      s'.vg.cf = some (decide (32 * k < (offOf sp0 ap k).toNat)) ∧
      s'.vg.wr = ⟨sp0 - BitVec.ofNat 64 48, 56⟩ :: rest ∧
      s'.vg.mem = pushes s.vg.mem sp0 s.vg.gpr ∧
      (∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → s'.vg.gpr r = s.vg.gpr r) ∧ others s'.vg = others s.vg ∧
      s'.vg.mxcsr = s.vg.mxcsr ∧ s'.vg.xmm = s.vg.xmm ∧ s'.lo = s.lo := by
  apply ex_of_eq
  · rw [execBlock_acc]
    shead_run
    iterate 6 (rw [moveSp_down]; shead_run; all_goals (first | shead_disch | skip))
    rfl
  · rfl
  · simp only [gpr_setReg, gpr_setWr, gpr_setMem, gpr_arithFlags, gpr_setFlags, wr_setReg, wr_setWr, wr_setMem,
      wr_arithFlags, wr_setFlags, mem_setReg, mem_setWr, mem_setMem, mem_arithFlags, mem_setFlags, others_setReg,
      others_setWr, others_setMem, others_arithFlags, others_setFlags, cf_arithFlags, reduceCtorEq, ↓reduceIte, hrsp]
    repeat' apply And.intro
    all_goals first
      | exact True.intro
      | (unfold pushes; rfl)
      | exact off_eq sp0 ap k
      | (rw [off_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; done)
      | (simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]; bv_omega)
      | (intro r hr
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
         simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte])
      | (simp only [xmm_setReg, xmm_setMem, xmm_arithFlags, xmm_setFlags, xmm_setWr])
      | (apply others_mxcsr
         simp only [others_setReg, others_setWr, others_setMem, others_arithFlags, others_setFlags])


/-! ## The frame's bottom -/

/-- The bottom `spAlt` leaves: `16k + 112` bytes below the stack pointer, less what `ap`'s offset exceeds
`4032 - 16k` by, if it does. -/
def altR (k : Nat) : Addr := 4032#64 - BitVec.ofNat 64 (16 * k)

theorem alt_eq (k : Nat) : 0 - BitVec.ofNat 64 (8 * k) + (0 - BitVec.ofNat 64 (8 * k)) + 4032#64 = altR k := by
  unfold altR
  rw [show 16 * k = 8 * k + 8 * k by omega, ← BitVec.ofNat_add_ofNat]
  generalize BitVec.ofNat 64 (8 * k) = x
  bv_omega

def bOf (sp0 ap : Addr) (k : Nat) : Addr :=
  if 32 * k < (offOf sp0 ap k).toNat then
    sp0 - BitVec.ofNat 64 (16 * k + 112) -
      (if (offOf sp0 ap k).toNat < (altR k).toNat then 0 else offOf sp0 ap k - altR k)
  else sp0 - (offOf sp0 ap k + BitVec.ofNat 64 (16 * k + 112))

set_option hygiene false in
/-- Runs a block of register instructions. -/
syntax "reg_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| reg_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 1000000 }) only [$xs,*, execAcc_cons, execAcc_nil, Rind.X86_64.exec,
      Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs, VG.X86_64.exec, execAlu, execCmov, VG.X86_64.eval, readSrc,
      Option.map_some, Option.bind_some, State.ea, Rind.X86_64.Mul4x.m, Rind.X86_64.Mul4x.mx, ofInt_lit,
      Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow, mul_ofNat_one, ofNat_zero, add_zero',
      signExtend_m64, signExtend_4032, signExtend_zero, signExtend_zero', Nat.reduceAdd, Nat.reduceSub,
      Nat.reducePow, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags, rd_arithFlags,
      wr_arithFlags, cf_arithFlags, cf_setReg, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append])

theorem spNear_ok (s : S) (k : Nat) (sp0 ap : Addr)
    (hrbp : s.vg.gpr .rbp = sp0 - BitVec.ofNat 64 48) (hr9 : s.vg.gpr .r9 = 0 - BitVec.ofNat 64 (8 * k))
    (hr11 : s.vg.gpr .r11 = offOf sp0 ap k) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.spNear s = some (s', []) ∧
      s'.vg.gpr .rbp = sp0 - (offOf sp0 ap k + BitVec.ofNat 64 (16 * k + 112)) ∧ s'.vg.wr = s.vg.wr ∧
      FrameS s s' [.rbp] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    reg_run [Rind.X86_64.Sqrx8xMont.spNear, hrbp, hr9, hr11, neg_mul2, linNear, BitVec.ofNat_add_ofNat]
    rfl
  · rfl
  · refine ⟨by simp only [gpr_setReg, ↓reduceIte], rfl, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ↓reduceIte]

theorem spAlt_ok (s : S) (k : Nat) (sp0 ap : Addr)
    (hrbp : s.vg.gpr .rbp = sp0 - BitVec.ofNat 64 48) (hr9 : s.vg.gpr .r9 = 0 - BitVec.ofNat 64 (8 * k))
    (hr11 : s.vg.gpr .r11 = offOf sp0 ap k) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8xMont.spAlt s = some (s', []) ∧
      s'.vg.gpr .rbp = sp0 - BitVec.ofNat 64 (16 * k + 112) -
        (if (offOf sp0 ap k).toNat < (altR k).toNat then 0 else offOf sp0 ap k - altR k) ∧
      s'.vg.wr = s.vg.wr ∧ FrameS s s' [.rbp, .r10, .r11] := by
  by_cases hc : (offOf sp0 ap k).toNat < (altR k).toNat <;>
  · apply ex_of_eq
    · rw [execBlock_acc]
      reg_run [Rind.X86_64.Sqrx8xMont.spAlt, hrbp, hr9, hr11, neg_mul2, lin112, BitVec.ofNat_add_ofNat, alt_eq, hc,
        decide_true, decide_false]
      rfl
    · rfl
    · refine ⟨by simp only [gpr_setReg, ↓reduceIte, hc], rfl, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ↓reduceIte]

theorem offOf_lt' (sp0 ap : Addr) (k : Nat) : (offOf sp0 ap k).toNat < 4096 := offOf_lt sp0 ap k

/-- `bOf`'s bounds: between `16k + 112` and `48k + 112` bytes below the stack pointer. -/
theorem bOf_toNat (sp0 ap : Addr) (k : Nat) (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) (h : 48 * k + 176 ≤ sp0.toNat) :
    sp0.toNat - (48 * k + 112) ≤ (bOf sp0 ap k).toNat ∧ (bOf sp0 ap k).toNat ≤ sp0.toNat - (16 * k + 112) := by
  have ho := offOf_lt sp0 ap k
  have hs := sp0.isLt
  unfold bOf
  generalize offOf sp0 ap k = o at ho ⊢
  have hR : (altR k).toNat = (4032 + (2 ^ 64 - 16 * k)) % 2 ^ 64 := by
    unfold altR; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  split
  · split
    · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
      omega
    · rename_i h1 h2
      rw [hR] at h2
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hR]
      omega
  · simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- The frame: `bOf` aligned down to 64. -/
def fpOf (sp0 ap : Addr) (k : Nat) : Addr := bOf sp0 ap k &&& BitVec.ofNat 64 18446744073709551552

theorem and_mask6 (x : BitVec 64) : x &&& BitVec.ofNat 64 18446744073709551552 = (x >>> 6) <<< 6 := by
  rw [BitVec.shiftLeft_ushiftRight]; rfl

theorem fpOf_toNat (sp0 ap : Addr) (k : Nat) (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) (h : 48 * k + 176 ≤ sp0.toNat) :
    (fpOf sp0 ap k).toNat % 64 = 0 ∧ (fpOf sp0 ap k).toNat + 16 * k + 112 ≤ sp0.toNat ∧
      sp0.toNat ≤ (fpOf sp0 ap k).toNat + 48 * k + 175 := by
  have hb := bOf_toNat sp0 ap k hk8 hk h
  unfold fpOf
  rw [and_mask6, toNat_shr_shl]
  generalize (bOf sp0 ap k).toNat = b at hb
  have := Nat.div_add_mod b 64
  have := Nat.mod_lt b (show 64 > 0 by norm_num)
  refine ⟨by simp, by omega, by omega⟩

/-- `frame`'s instructions before the stack move. -/
def frameA : List Ins :=
  [.vg (.alu .and .rbp (.imm (-64))),
   .vg (.mov .r11 (.reg .rsp)),
   .vg (.alu .sub .r11 (.reg .rbp)),
   .vg (.alu .and .r11 (.imm (-4096)))]

theorem frame_split : Rind.X86_64.Sqrx8xMont.frame = frameA ++ mulx4x.prologueB := rfl

theorem frameA_ok (s : S) (sp0 ap : Addr) (k : Nat)
    (hrsp : s.vg.gpr .rsp = sp0 - BitVec.ofNat 64 48) (hrbp : s.vg.gpr .rbp = bOf sp0 ap k) :
    ∃ s', execBlock I frameA s = some (s', []) ∧
      s'.vg.gpr .rbp = fpOf sp0 ap k ∧ s'.vg.gpr .r11 = pagesOf sp0 (fpOf sp0 ap k) ∧
      s'.vg.wr = s.vg.wr ∧ s'.lo = s.lo ∧ FrameS s s' [.rbp, .r11] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    reg_run [frameA, hrsp, hrbp, signExtend_m4096]
    rfl
  · rfl
  · refine ⟨rfl, rfl, rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ↓reduceIte]

theorem walk_eq : Rind.X86_64.Sqrx8xMont.walk = Rind.X86_64.Mulx4x.walk := rfl

/-- The prologue's trace through the walk, of the stack pointer, `ap`, `n0`'s address, and `k`. -/
def headTrace (sp0 ap n0p : Addr) (k : Nat) : List Leak :=
  let fp := fpOf sp0 ap k
  mulx4x.prologueATrace sp0 n0p ++ (Leak.branch (decide (32 * k < (offOf sp0 ap k).toNat)) :: ([] ++
    ([Leak.addr (pagesOf sp0 fp + fp)] ++ mulx4x.walkTrace fp ((pagesOf sp0 fp).toNat / 4096))))

/-- The branch that picks the frame's bottom. -/
abbrev spIte : Prog I :=
  .ite (Rind.X86_64.Cond.vg .b) (.seq (.block [.align 32]) (.block Rind.X86_64.Sqrx8xMont.spAlt))
    (.block Rind.X86_64.Sqrx8xMont.spNear)

set_option maxHeartbeats 1000000 in
theorem head_ok (s : S) (k : Nat) (sp0 ap n0p n0' : Addr) (rest : List Region)
    (hk8 : 8 ≤ k) (hk : k < 2 ^ 29) (hlo : s.lo.toNat + 48 * k + 184 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = sp0) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k) (hr8 : s.vg.gpr .r8 = n0p)
    (hrsi : s.vg.gpr .rsi = ap)
    (hwr : s.vg.wr = ⟨sp0, 8⟩ :: rest) (rN0 : ⟨n0p, 8⟩ ∈ s.vg.rd) (hn0p : n0p.toNat + 8 ≤ 2 ^ 64)
    (sepN0 : n0p.toNat + 8 ≤ sp0.toNat - 48 ∨ sp0.toNat + 8 ≤ n0p.toNat)
    (hn0 : s.vg.mem.readW n0p 64 = n0') :
    ∃ s₁ s₂ s₃ s', Exec I (.block Rind.X86_64.Sqrx8xMont.prologue) s (mulx4x.prologueATrace sp0 n0p) s₁ ∧
      Exec I spIte s₁ [.branch (decide (32 * k < (offOf sp0 ap k).toNat))] s₂ ∧
      Exec I (.block Rind.X86_64.Sqrx8xMont.frame) s₂
        [.addr (pagesOf sp0 (fpOf sp0 ap k) + fpOf sp0 ap k)] s₃ ∧
      Exec I (.ite Rind.X86_64.Cond.a (.loop walkBody Rind.X86_64.Cond.a) (.block [])) s₃
        (mulx4x.walkTrace (fpOf sp0 ap k) ((pagesOf sp0 (fpOf sp0 ap k)).toNat / 4096)) s' ∧
      s'.vg.gpr .rsp = fpOf sp0 ap k ∧ s'.vg.gpr .rax = sp0 ∧ s'.vg.gpr .r8 = n0' ∧
      s'.vg.gpr .r9 = 0 - BitVec.ofNat 64 (8 * k) ∧
      s'.vg.wr = ⟨fpOf sp0 ap k, sp0.toNat + 8 - (fpOf sp0 ap k).toNat⟩ :: rest ∧
      s'.vg.mem = pushes s.vg.mem sp0 s.vg.gpr ∧
      (∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → s'.vg.gpr r = s.vg.gpr r) ∧
      others s'.vg = others s.vg ∧ s'.vg.mxcsr = s.vg.mxcsr ∧ s'.vg.xmm = s.vg.xmm ∧ s'.lo = s.lo := by
  obtain ⟨s₁, hxA, a_sp, a_ax, a8, a9, a10, abp, a11, acf, awr, amem, ag, aoth, amx, axm, alo⟩ :=
    prologue_ok s k sp0 ap n0p n0' rest hk (by omega) hsp hrsp hr9 hr8 hrsi hwr rN0 hn0p sepN0 hn0
  -- The frame's bottom.
  have hite : ∃ s₂, Exec I spIte s₁ [.branch (decide (32 * k < (offOf sp0 ap k).toNat))] s₂ ∧
      s₂.vg.gpr .rbp = bOf sp0 ap k ∧ s₂.vg.wr = s₁.vg.wr ∧ FrameS s₁ s₂ [.rbp, .r10, .r11] := by
    by_cases hc : 32 * k < (offOf sp0 ap k).toNat
    · obtain ⟨s₂, hx, h_bp, hw, hF⟩ := spAlt_ok s₁ k sp0 ap abp a9 a11
      have hs := Exec.seq (Exec.block (M := I) (is := [.align 32]) (s := s₁) (s' := s₁) (t := []) rfl)
        (Exec.block hx)
      refine ⟨s₂, ?_, by rw [h_bp]; unfold bOf; simp only [hc, ↓reduceIte], hw, hF⟩
      simp only [hc, decide_true]
      exact Exec.iteT (by simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, acf, hc, decide_true]) hs
    · obtain ⟨s₂, hx, h_bp, hw, hF⟩ := spNear_ok s₁ k sp0 ap abp a9 a11
      refine ⟨s₂, ?_, by rw [h_bp]; unfold bOf; simp only [hc, ↓reduceIte], hw,
        ⟨fun r hr => hF.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1),
          hF.mem, hF.others, hF.xmm, hF.mxcsr, hF.lo⟩⟩
      simp only [hc, decide_false]
      exact Exec.iteF (by simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, acf, hc, decide_false])
        (Exec.block hx)
  obtain ⟨s₂, hx2, b_bp, bwr, bF⟩ := hite
  obtain ⟨s₂', hxF, f_bp, f11, fwr, flo, fF⟩ :=
    frameA_ok s₂ sp0 ap k ((bF.gpr .rsp (by decide)).trans a_sp) b_bp
  have hfp := fpOf_toNat sp0 ap k hk8 hk (by omega)
  generalize fpOf sp0 ap k = fp at hfp f_bp f11 ⊢
  obtain ⟨T0, T1, T2⟩ := hfp
  have hP := pagesOf_toNat sp0 fp (by omega)
  have hq : (sp0 - BitVec.ofNat 64 48).toNat = sp0.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  generalize pagesOf sp0 fp = P at hP f11 ⊢
  have p1 := Nat.div_add_mod (sp0.toNat - 48 - fp.toNat) 4096
  have p2 := Nat.mod_lt (sp0.toNat - 48 - fp.toNat) (show 4096 > 0 by norm_num)
  have p3 : P.toNat ≤ sp0.toNat - 48 - fp.toNat ∧ P.toNat % 4096 = 0 := by rw [hP]; omega
  clear p1 p2
  have hTP : (P + fp).toNat = fp.toNat + P.toNat := by rw [BitVec.toNat_add]; omega
  have hlo2 : s₂'.lo = s.lo := by rw [flo, bF.lo, alo]
  have hwr2 : s₂'.vg.wr = ⟨sp0 - BitVec.ofNat 64 48, 56⟩ :: rest := by
    rw [fwr, bwr, awr]
  obtain ⟨s₃, hxB, c_sp, cbp, cwr, ccf, czf, cF⟩ :=
    prologueB_ok s₂' (sp0 - BitVec.ofNat 64 48) fp P 56 rest
      ((fF.gpr .rsp (by decide)).trans ((bF.gpr .rsp (by decide)).trans a_sp)) f_bp f11 hwr2 (by omega)
      (by omega) (by rw [hlo2]; omega)
  have hxP : execBlock I Rind.X86_64.Sqrx8xMont.frame s₂ = some (s₃, [.addr (P + fp)]) := by
    rw [frame_split, execBlock_append, hxF]
    simp only [Option.bind_some, hxB, Option.map_some, List.nil_append]
  have hPf : P + fp = fp + P := BitVec.add_comm _ _
  set m := P.toNat / 4096 with hm
  have hPm : P = BitVec.ofNat 64 (4096 * m) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  have hev : I.eval Rind.X86_64.Cond.a s₃ = some (!decide (m = 0)) := by
    simp only [Rind.X86_64.isa, Rind.X86_64.eval, ccf, czf, Option.bind_some, Option.map_some]
    have h1 : decide ((P + fp).toNat < fp.toNat) = false := by rw [hTP]; simp
    have h2 : (P + fp - fp == 0) = decide (m = 0) := by
      rw [show P + fp - fp = P by bv_omega]
      by_cases h : m = 0
      · have hP0 : P = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
        simp only [h, hP0, decide_true, beq_self_eq_true]
      · have hP0 : P ≠ 0 := fun h' => by rw [h', show (0 : BitVec 64).toNat = 0 from rfl] at hm; exact h hm
        simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, hP0, not_false_eq_true]
    rw [h1, h2, Bool.not_false, Bool.true_and]
  have hwalk : ∃ s₄, Exec I (.ite Rind.X86_64.Cond.a (.loop walkBody Rind.X86_64.Cond.a) (.block [])) s₃
      (mulx4x.walkTrace fp m) s₄ ∧ s₄.vg.gpr .rsp = fp ∧ s₄.vg.wr = ⟨fp, sp0.toNat + 8 - fp.toNat⟩ :: rest ∧
      FrameS s₃ s₄ [.rsp, .r10] := by
    by_cases h0 : m = 0
    · have hP0 : P = 0 := by rw [hPm, h0]; rfl
      refine ⟨s₃, ?_, by rw [c_sp, hP0]; exact BitVec.zero_add _, ?_, FrameS.refl _ _⟩
      · simp only [mulx4x.walkTrace, h0, ↓reduceIte]
        exact Exec.iteF (by rw [hev, h0]; rfl) (Exec.block rfl)
      · have hP0n : P.toNat = 0 := by omega
        rw [cwr, hTP, hq, hP0n, hP0]
        simp only [List.cons.injEq, Region.mk.injEq, and_true]
        exact ⟨BitVec.zero_add _, by omega⟩
    · have hI : mulx4x.WalkInv s₃ s₃ fp sp0 rest m 0 := by
        refine ⟨by rw [c_sp, hPf, hPm]; rfl, cbp, ?_, FrameS.refl _ _⟩
        simp only [Nat.sub_zero]
        rw [cwr, ← hPm, ← hPf, hTP, hq]
        simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]
        omega
      obtain ⟨s₄, hx4, hI4⟩ := walk_loop s₃ fp sp0 rest m (by omega) (by omega) hsp
        (by rw [cF.lo, hlo2]; omega) hI
      refine ⟨s₄, ?_, ?_, ?_, hI4.frame⟩
      · simp only [mulx4x.walkTrace, h0, ↓reduceIte]
        exact Exec.iteT (by rw [hev]; simp [h0]) hx4
      · rw [hI4.rsp, Nat.sub_self, Nat.mul_zero]; exact BitVec.add_zero _
      · rw [hI4.wr, Nat.sub_self, Nat.mul_zero]; simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  obtain ⟨s₄, hx4, d_sp, dwr, dF⟩ := hwalk
  have F := cF.trans dF
  have K : ∀ r, r ∉ [Reg.rsp, .rbp, .r10, .r11] → s₄.vg.gpr r = s₁.vg.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [F.gpr r (by simp [hr.1, hr.2.2.1]), fF.gpr r (by simp [hr.2.1, hr.2.2.2]),
      bF.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2])]
  refine ⟨s₁, s₂, s₃, s₄, Exec.block hxA, hx2, Exec.block hxP, hx4, d_sp, ?_, ?_, ?_, dwr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K .rax (by decide), a_ax]
  · rw [K .r8 (by decide), a8]
  · rw [K .r9 (by decide), a9]
  · rw [F.mem, fF.mem, bF.mem, amem]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K r (by simp [hr.1, hr.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
      ag r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2])]
  · rw [F.others, fF.others, bF.others, aoth]
  · rw [F.mxcsr, fF.mxcsr, bF.mxcsr, amx]
  · rw [F.xmm, fF.xmm, bF.xmm, axm]
  · rw [F.lo, hlo2]

end rind.x86_64.sqrx8xmont
