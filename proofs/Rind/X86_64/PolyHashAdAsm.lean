import RindIsa.X86_64.PolyHashAd
import Rind.X86_64.PolyHashAdModel

open VG VG.X86_64 Rind.X86_64.PolyHashAd rind.x86_64.asm rind.spec.poly1305

set_option linter.unusedSimpArgs false

/-!
# `poly_hash_ad_internal`'s blocks

Each block of `PolyHashAd.prog` run on rind's x86_64 model: its trace, and
what it leaves in the registers it changes.
-/

namespace rind.x86_64.polyhashad

/-- The immediates this routine sign-extends, as words. -/
theorem sx1 : (1 : BitVec 32).signExtend 64 = 1#64 := by decide
theorem sx13 : (13 : BitVec 32).signExtend 64 = 13#64 := by decide
theorem sx16 : (16 : BitVec 32).signExtend 64 = 16#64 := by decide
theorem add_neg_one (c : BitVec 64) : c + 18446744073709551615#64 = c - 1#64 := by bv_omega

/-- A readable byte loads as memory holds it. -/
theorem load8_of {s : VG.X86_64.State} {a : Addr} (h : InRegions (s.rd ++ s.wr) a 1) :
    s.load8 a = some (s.mem a) := by
  simp [VG.X86_64.State.load8, h]

set_option hygiene false in
/-- Discharges the side conditions of a block's run. -/
macro "pha_disch" : tactic => `(tactic| no_recover first
  | decide
  | assumption
  | (try simp only [rd_setReg, wr_setReg, rd_execMul, wr_execMul, rd_execImul, wr_execImul, rd_arithFlags,
        wr_arithFlags, rd_setFlags, wr_setFlags, rd_setMem, wr_setMem]) <;> first
      | assumption
      | omega)

/-- The lemmas that run a block of this routine. -/
syntax "pha_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| pha_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := pha_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      load64_of, Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.addrs, srcAddrs,
      VG.X86_64.exec, execAlu, execShift, execShld, readSrc, load8_of, Option.map_some, Option.bind_some, decide_carry,
      State.ea, m, ofInt_lit, Int.reduceNeg, Int.reduceMod, Int.reduceToNat, Int.reducePow,
      BitVec.xor_self, BitVec.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reducePow, Nat.add_zero,
      Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, ofNat_zero, BitVec.add_zero, add_zero', zero_add',
      signExtend_zero, signExtend_zero', decide_carry', sx1, sx13, sx16, add_neg_one,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, cf_setReg, gpr_arithFlags, mem_arithFlags, rd_arithFlags,
      wr_arithFlags, cf_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, gpr_setMem, mem_setMem,
      rd_setMem, wr_setMem, cf_setMem, gpr_execMul, mem_execMul, rd_execMul, wr_execMul,
      gpr_execImul, mem_execImul, rd_execImul, wr_execImul, reduceCtorEq, ↓reduceIte, List.map_nil, List.map_cons,
      List.append_nil, List.nil_append, List.cons_append])

/-- The tactic that reads what a block leaves: its registers, memory, and
frame, each by `rfl` once `simp` has read through the folded updates. -/
syntax "pha_out" : tactic
macro_rules
  | `(tactic| pha_out) => `(tactic| (
    repeat' apply And.intro
    all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
      others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
      mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_execMul, mem_execMul, wr_execMul, xmm_execMul,
      others_execMul, gpr_execImul, mem_execImul, wr_execImul, xmm_execImul, others_execImul, zf_setReg, cf_setReg,
      zf_arithFlags, cf_arithFlags, reduceCtorEq, ↓reduceIte, *]
    all_goals rfl))

/-- `r`, the two words at `kp`, which `rbp` points to. -/
structure Key (s : S) (kp r0 r1 : BitVec 64) : Prop where
  rbp : s.vg.gpr .rbp = kp
  rd0 : InRegions (s.vg.rd ++ s.vg.wr) kp 8
  rd1 : InRegions (s.vg.rd ++ s.vg.wr) (kp + 8#64) 8
  m0 : s.vg.mem.readW kp 64 = r0
  m1 : s.vg.mem.readW (kp + 8#64) 64 = r1

/-- `mul`'s trace: the words of `r`, each read twice. -/
def mulTrace (kp : Addr) : List Leak := [.addr kp, .addr kp, .addr (kp + 8#64), .addr (kp + 8#64)]

set_option maxHeartbeats 8000000 in
/-- `mul` leaves `mulOut` of the accumulator and `r` in `(r10, r11, r12)`. -/
theorem mul_ok (s : S) (kp r0 r1 : BitVec 64) (k : Key s kp r0 r1) :
    let o := mulOut (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) r0 r1
    ∃ s', execBlock I mul s = some (s', mulTrace kp) ∧
      s'.vg.gpr .r10 = o.1 ∧ s'.vg.gpr .r11 = o.2.1 ∧ s'.vg.gpr .r12 = o.2.2 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.rax, .rdx, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hrbp, hk0, hk1, hm0, hm1⟩ := k
  intro o
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [mul, hrbp, hm0, hm1]
    rfl
  · rfl
  · pha_out

/-- `init` zeroes the accumulator and compares the length with 13. -/
theorem init_ok (s : S) :
    ∃ s', execBlock I init s = some (s', []) ∧
      s'.vg.gpr .r10 = 0 ∧ s'.vg.gpr .r11 = 0 ∧ s'.vg.gpr .r12 = 0 ∧
      s'.vg.zf = some (s.vg.gpr .r8 - 13#64 == 0) ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.r10, .r11, .r12] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [init]
    rfl
  · rfl
  · pha_out

/-- `cmp r8, k` sets ZF and CF from `r8 - k`, and changes no memory or
register. It also sets SF and OF, which no block here reads. -/
theorem cmp_ok (s : S) (k : BitVec 32) :
    ∃ s', execBlock I [.vg (.alu .cmp .r8 (.imm k))] s = some (s', []) ∧
      s'.vg.zf = some (s.vg.gpr .r8 - k.signExtend 64 == 0) ∧
      s'.vg.cf = some (decide ((s.vg.gpr .r8).toNat < (k.signExtend 64).toNat)) ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [and_self]
    rfl
  · rfl
  · pha_out

/-- `load13` loads the 13-byte AAD at `c` and the bit above it into the accumulator. -/
theorem load13_ok (s : S) (c : Addr) (hrcx : s.vg.gpr .rcx = c)
    (h0 : InRegions (s.vg.rd ++ s.vg.wr) c 8) (h1 : InRegions (s.vg.rd ++ s.vg.wr) (c + 5#64) 8) :
    ∃ s', execBlock I load13 s = some (s', [.addr c, .addr (c + 5#64)]) ∧
      s'.vg.gpr .r10 = s.vg.mem.readW c 64 ∧ s'.vg.gpr .r11 = s.vg.mem.readW (c + 5#64) 64 >>> 24 ∧
      s'.vg.gpr .r12 = 1#64 ∧ s'.vg.mem = s.vg.mem ∧ Frame s s' [.r10, .r11, .r12] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [load13, hrcx]
    rfl
  · rfl
  · pha_out

/-- `addBlock` adds the block at `c` and the bit above it to the accumulator. -/
theorem addBlock_ok (s : S) (c : Addr) (hrcx : s.vg.gpr .rcx = c)
    (h0 : InRegions (s.vg.rd ++ s.vg.wr) c 8) (h1 : InRegions (s.vg.rd ++ s.vg.wr) (c + 8#64) 8) :
    let o := addT (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.mem.readW c 64)
      (s.vg.mem.readW (c + 8#64) 64)
    ∃ s', execBlock I addBlock s = some (s', [.addr c, .addr (c + 8#64)]) ∧
      s'.vg.gpr .r10 = o.1 ∧ s'.vg.gpr .r11 = o.2.1 ∧ s'.vg.gpr .r12 = o.2.2 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.r10, .r11, .r12] := by
  intro o
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [addBlock, hrcx]
    rfl
  · rfl
  · pha_out

/-- `next` steps `rcx` and `r8` a block on and compares what is left with 16. -/
theorem next_ok (s : S) :
    ∃ s', execBlock I next s = some (s', []) ∧
      s'.vg.gpr .rcx = s.vg.gpr .rcx + 16#64 ∧ s'.vg.gpr .r8 = s.vg.gpr .r8 - 16#64 ∧
      s'.vg.cf = some (decide ((s.vg.gpr .r8 - 16#64).toNat < 16)) ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.rcx, .r8] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [next]
    rfl
  · rfl
  · pha_out

/-- `tailInit` clears `(r13, r14)` and points `rcx` past the AAD. -/
theorem tailInit_ok (s : S) :
    ∃ s', execBlock I tailInit s = some (s', []) ∧
      s'.vg.gpr .r13 = 0 ∧ s'.vg.gpr .r14 = 0 ∧ s'.vg.gpr .rcx = s.vg.gpr .rcx + s.vg.gpr .r8 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.r13, .r14, .r15, .rcx] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [tailInit]
    rfl
  · rfl
  · pha_out

/-- `tailByte` shifts the byte before `c` into `(r13, r14)` and steps back a byte. -/
theorem tailByte_ok (s : S) (c : Addr) (hrcx : s.vg.gpr .rcx = c) (h : InRegions (s.vg.rd ++ s.vg.wr) (c - 1#64) 1) :
    let o := tailStep (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.mem (c - 1#64))
    ∃ s', execBlock I tailByte s = some (s', [.addr (c - 1#64)]) ∧
      s'.vg.gpr .r13 = o.1 ∧ s'.vg.gpr .r14 = o.2 ∧ s'.vg.gpr .rcx = c - 1#64 ∧
      s'.vg.gpr .r8 = s.vg.gpr .r8 - 1#64 ∧ s'.vg.zf = some (s.vg.gpr .r8 - 1#64 == 0) ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.r13, .r14, .r15, .rcx, .r8] := by
  intro o
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [tailByte, hrcx]
    rfl
  · rfl
  · pha_out

/-- `addTail` adds the partial block in `(r13, r14)` and the bit above it. -/
theorem addTail_ok (s : S) :
    let o := addT (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13) (s.vg.gpr .r14)
    ∃ s', execBlock I addTail s = some (s', []) ∧
      s'.vg.gpr .r10 = o.1 ∧ s'.vg.gpr .r11 = o.2.1 ∧ s'.vg.gpr .r12 = o.2.2 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.r10, .r11, .r12] := by
  intro o
  apply ex_of_eq
  · rw [execBlock_acc]
    pha_run [addTail]
    rfl
  · rfl
  · pha_out

end rind.x86_64.polyhashad
