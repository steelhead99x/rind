import VerifiedGarbage.TCB.AArch64.Encode

/-!
# rind's extension of VG's AArch64 model

**Trusted.** VG's model (`VerifiedGarbage/TCB/AArch64/`) covers the
instructions VG's own code uses. rind proves code VG did not write, aws-lc's
assembly among it, which also uses the frame pointer `x29`, the multiple
structure forms of LD1 and ST1, LD4R, aws-lc's frame of `x29` and `x30`, a
frame of `d8`–`d15`, the immediate forms of SUBS, ADDS and AND, the zero
register as an operand, post- and pre-indexed loads and stores, UMOV of a
byte, and B.cond. This model is VG's with those added: its state is VG's with `x29`, and its
instructions are VG's, run by VG's semantics on VG's part of the state, and
those below, each transcribing the pseudocode of the Arm Architecture
Reference Manual for A-profile (DDI 0487) the docs cite, in VG's style, so
that the leakage model of `TCB/Code.lean` applies unchanged: every memory
access faults outside the state's regions, and leaks its address.

`admin/prove vg` cosimulates each instruction of every program in
`RindIsa/` against the CPU (`Cosim/Rind.lean`), and `admin/prove lean`
checks that each program's bytes (`layout`) are the ones rind's build emits.
-/

namespace Rind.AArch64

open VG VG.AArch64

/-- VG's machine state with the frame pointer `x29`, which VG's model leaves
out (see its module docs) and aws-lc's frames save and restore. -/
structure State where
  vg : VG.AArch64.State
  x29 : BitVec 64

inductive Instr
  /-- An instruction of VG's model, with VG's semantics. -/
  | vg (i : VG.AArch64.Instr)
  /-- `ld1 {vt.<a>, …}, [xn]` with the `cnt` registers from `t` (LD1
  (multiple structures), no offset), or `ld1 {vt.<a>, …}, [xn], #(16 * cnt)`
  if `post` (post-index, immediate offset) -/
  | ld1 (cnt : Nat) (a : VArr) (t : VReg) (n : Reg) (post : Bool)
  /-- `st1 {vt.<a>, …}, [xn]` (ST1 (multiple structures)), as `ld1` -/
  | st1 (cnt : Nat) (a : VArr) (t : VReg) (n : Reg) (post : Bool)
  /-- `stp x29, x30, [sp, #-16]!` (STP, 64-bit, pre-index) -/
  | stpFrame
  /-- `mov x29, sp` (alias of ADD (immediate), `add x29, sp, #0`) -/
  | movFp
  /-- `ldr x29, [sp], #16` (LDR (immediate), 64-bit, post-index) -/
  | ldrFp
  /-- `ld4r {vt.4s - v(t+3).4s}, [xn]`, or `[xn], #16` if `post` (LD4R, 32-bit
  elements, `Q = 1`, no offset or post-index by the immediate) -/
  | ld4r (t : VReg) (n : Reg) (post : Bool)
  /-- `cmp xn, #imm` (alias of SUBS (immediate), 64-bit, `Rd = 31`, no shift) -/
  | cmpImm (n : Reg) (imm : Nat)
  /-- `subs xd, xn, #imm` (SUBS (immediate), 64-bit, no shift) -/
  | subsImm (d n : Reg) (imm : Nat)
  /-- `adds xd, xn, #imm` (ADDS (immediate), 64-bit, no shift), which the
  assembler also writes for `subs xd, xn, #-imm` -/
  | addsImm (d n : Reg) (imm : Nat)
  /-- `and xd, xn, #mask` (AND (immediate), 64-bit, `N = 1`): the mask of
  `ones` one bits, from bit 0, rotated right by `rot` -/
  | andImm (d n : Reg) (ones rot : Nat)
  /-- `adc xd, xn, xzr` (ADC, 64-bit, `Rm = 31`) -/
  | adcZr (d n : Reg)
  /-- `neg xd, xm` (alias of SUB (shifted register), 64-bit, `Rn = 31`, no shift) -/
  | neg (d m : Reg)
  /-- `mov xd, xm` (alias of ORR (shifted register), 64-bit, `Rn = 31`, no shift) -/
  | movReg (d m : Reg)
  /-- `ldp xt1, xt2, [xn], #imm` (LDP, 64-bit, post-index, `imm` a multiple of 8
  less than 512) -/
  | ldpPost (t1 t2 n : Reg) (imm : Nat)
  /-- `ldrb wt, [xn, xm]` (LDRB (register), `option = 011`, `S = 0`) -/
  | ldrbReg (t n m : Reg)
  /-- `ldrb wt, [xn, #-1]!` (LDRB (immediate), pre-index, `imm9 = -1`) -/
  | ldrbPreDec (t n : Reg)
  /-- `strb wt, [xn], #1` (STRB (immediate), post-index, `imm9 = 1`) -/
  | strbPostInc (t n : Reg)
  /-- `umov wd, vn.b[i]` (UMOV, 8-bit element) -/
  | umovB (d : Reg) (n : VReg) (i : Nat)
  /-- `stp dt1, dt2, [sp, #-imm]!` (STP (SIMD&FP), 64-bit, pre-index) -/
  | stpDPre (t1 t2 : VReg) (imm : Nat)
  /-- `stp dt1, dt2, [sp, #off]` (STP (SIMD&FP), 64-bit, signed offset) -/
  | stpD (t1 t2 : VReg) (off : Nat)
  /-- `ldp dt1, dt2, [sp, #off]` (LDP (SIMD&FP), 64-bit, signed offset) -/
  | ldpD (t1 t2 : VReg) (off : Nat)
  /-- `ldp dt1, dt2, [sp], #imm` (LDP (SIMD&FP), 64-bit, post-index) -/
  | ldpDPost (t1 t2 : VReg) (imm : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions: VG's CBZ and CBNZ, and B.cond on a condition code
(DDI 0487 C6.2, "B.cond": the branch is taken iff
`ConditionHolds(cond)`, `CondCode.holds`). -/
inductive Cond
  | vg (c : VG.AArch64.Cond)
  | flags (c : CondCode)
  deriving DecidableEq, Repr

/-- Load the `k` vector registers from `t`, 16 bytes each, from `a` on.
DDI 0487 C7.2, "LD1 (multiple structures)": for each register `r` and
element `e`, `Elem[V[t + r], e] = Mem[address + offs, ebytes]`, `offs`
advancing `ebytes` an element and `t` wrapping modulo 32 (`VReg.succ`).
Memory is little-endian, so whatever the arrangement, register `r` holds
the 16 bytes at `a + 16 r`, little-endian: what VG's `State.load` reads. -/
def ldVecs (g : VG.AArch64.State) (a : Addr) : VReg → Nat → Option VG.AArch64.State
  | _, 0 => some g
  | t, k + 1 => (g.load a 16).bind fun x => ldVecs (g.setV t x) (a + 16) t.succ k

/-- Store the `k` vector registers from `t` to `a` on, as `ldVecs` loads
them. DDI 0487 C7.2, "ST1 (multiple structures)": `Mem[address + offs,
ebytes] = Elem[V[t + r], e]`. -/
def stVecs (g : VG.AArch64.State) (a : Addr) : VReg → Nat → Option VG.AArch64.State
  | _, 0 => some g
  | t, k + 1 => (g.store a 16 (g.v t)).bind fun g' => stVecs g' (a + 16) t.succ k

/-- Load `k` vector registers from `t`, each the 32-bit element at `a + 4 r`
replicated to its four lanes. DDI 0487 C7.2, "LD4R": `selem = 4`, `replicate`:
for each structure element `s`, `element = Mem[address, ebytes]; V[t] =
Replicate(element, datasize)`, `address` advancing `ebytes`, `t` wrapping
modulo 32. -/
def ldReps (g : VG.AArch64.State) (a : Addr) : VReg → Nat → Option VG.AArch64.State
  | _, 0 => some g
  | t, k + 1 => (g.load a 4).bind fun x =>
    let w := x.setWidth 32
    ldReps (g.setV t (ofVWords w w w w)) (a + 4) t.succ k

/-- The 64-bit register `d<t>`: the low half of `v<t>`. -/
def dreg (g : VG.AArch64.State) (t : VReg) : BitVec 64 := (g.v t).setWidth 64

/-- Store `d<t1>` at `a` and `d<t2>` at `a + 8`, as STP (SIMD&FP), 64-bit,
does. -/
def stD (g : VG.AArch64.State) (a : Addr) (t1 t2 : VReg) : Option VG.AArch64.State :=
  (g.store a 8 (dreg g t1)).bind fun g => g.store (a + 8) 8 (dreg g t2)

/-- Load `d<t1>` from `a` and `d<t2>` from `a + 8`, as LDP (SIMD&FP), 64-bit,
does: a write of a 64-bit register zeroes the rest of the vector register
(`V[t, 64] = data`; DDI 0487 J1.2, `V[]`: the bits above the width written
become zero). `t1 = t2` is CONSTRAINED UNPREDICTABLE, so it faults. -/
def ldD (g : VG.AArch64.State) (a : Addr) (t1 t2 : VReg) : Option VG.AArch64.State :=
  if t1 = t2 then none else
  (g.load a 8).bind fun x => (g.load (a + 8) 8).map fun y =>
    (g.setV t1 (x.setWidth 128)).setV t2 (y.setWidth 128)

/-- The 64-bit mask of `ones` one bits rotated right by `rot`, as DDI 0487
J1.3 `DecodeBitMasks` gives it for `N = 1`, `imms = ones - 1`, `immr = rot`. -/
def bitMask (ones rot : Nat) : BitVec 64 := (BitVec.ofNat 64 (2 ^ ones - 1)).rotateRight rot

/-- The state after LD1 or ST1 of `cnt` registers through `n`: with `post`,
`n` advances by the bytes accessed (DDI 0487 C7.2, "LD1 (multiple
structures)", post-index, immediate: `offs = imm`, the `#<imm>` the
assembler requires to be `16 * cnt` for 128-bit registers; `if wback then
X[n, 64] = address + offs`). -/
def advance (g : VG.AArch64.State) (n : Reg) (base : Addr) (cnt : Nat) (post : Bool) :
    VG.AArch64.State :=
  if post then g.write .x n (base + BitVec.ofNat 64 (16 * cnt)) else g

/-- Semantics:
* VG's instructions: VG's `exec`, on VG's part of the state.
* "LD1 (multiple structures)", "ST1 (multiple structures)", 1 to 4
  registers (`selem = 1`, `rpt = cnt`): `ldVecs`, `stVecs`, `advance`.
  `address = X[n, 64]` is read before any write, and the accesses are of
  Normal memory, which need no alignment (`SCTLR_ELx.A` 0, as VG's model has
  it for `LDR (immediate, SIMD&FP)`).
* "STP" 64-bit, pre-index, `Rn = SP`, `imm7 = -2` (`offset = -16`):
  `address = SP[] + offset; Mem[address, 8] = X[29]; Mem[address + 8, 8] =
  X[30]; SP[] = address`.
* "ADD (immediate)", `Rd = 29`, `Rn = SP`, `imm12 = 0`: `X[29] = SP[]`.
* "LDR (immediate)" 64-bit, post-index, `Rn = SP`, `imm9 = 16`: `address =
  SP[]; X[29] = Mem[address, 8]; SP[] = address + 16`.

* "LD4R", 32-bit elements, `Q = 1`: `ldReps`; post-index by the immediate
  (`Rm = 31`), `X[n, 64] = address + 16`.
* "SUBS (immediate)", "ADDS (immediate)", 64-bit, `sh = 0`, `imm12 = imm`:
  `(result, nzcv) = AddWithCarry(X[n], NOT(imm), '1')` or `AddWithCarry(X[n],
  imm, '0')`, `PSTATE.<N,Z,C,V> = nzcv`, `X[d] = result` unless `d = 31`
  (`cmpImm`), VG's `flagsAdd` and `addWithCarry`.
* "AND (immediate)", 64-bit, `N = 1`: `X[d] = X[n] AND imm`, `imm` from
  `DecodeBitMasks` (`bitMask`).
* "ADC", `Rm = 31`: `X[d] = X[n] + 0 + PSTATE.C`; "SUB (shifted register)",
  `Rn = 31`: `X[d] = 0 - X[m]`; "ORR (shifted register)", `Rn = 31`: `X[d] =
  0 OR X[m]`.
* "LDP", 64-bit, post-index: `address = X[n]; X[t] = Mem[address, 8];
  X[t2] = Mem[address + 8, 8]; X[n] = address + imm`. `t = t2`, and `t` or
  `t2` equal to `n` with writeback, are CONSTRAINED UNPREDICTABLE, so they
  fault.
* "LDRB (register)", `option = 011` (LSL), `S = 0`: `address = X[n] + X[m];
  X[t] = ZeroExtend(Mem[address, 1])`.
* "LDRB (immediate)", pre-index, `imm9 = -1`: `address = X[n] - 1; X[t] =
  ZeroExtend(Mem[address, 1]); X[n] = address`; "STRB (immediate)",
  post-index, `imm9 = 1`: `address = X[n]; Mem[address, 1] = X[t]<7:0>;
  X[n] = address + 1`. `t = n` with writeback is CONSTRAINED UNPREDICTABLE,
  so it faults.
* "UMOV", 8-bit element: `X[d] = ZeroExtend(Elem[V[n], i, 8], 32)`.
* "STP (SIMD&FP)", "LDP (SIMD&FP)", 64-bit, `Rn = SP`: `stD`, `ldD`, at `SP +
  off`, or pre-index at `SP - imm` (`SP[] = address`), or post-index at `SP`
  (`SP[] = address + imm`).

An access through `sp` faults unless it is 16-byte aligned, as Linux's
SCTLR_EL1.SA0 makes it (DDI 0487 D1.3.10, "SP alignment checking"), and
AAPCS64 keeps it (§6.4.5.1, "SP mod 16 = 0"). -/
def exec : Instr → State → Option State
  | .vg i, s => (VG.AArch64.exec i s.vg).map fun g => { s with vg := g }
  | .ld1 cnt _ t n post, s =>
    if 1 ≤ cnt ∧ cnt ≤ 4 then
      (ldVecs s.vg (s.vg.gpr n) t cnt).map fun g =>
        { s with vg := advance g n (s.vg.gpr n) cnt post }
    else none
  | .st1 cnt _ t n post, s =>
    if 1 ≤ cnt ∧ cnt ≤ 4 then
      (stVecs s.vg (s.vg.gpr n) t cnt).map fun g =>
        { s with vg := advance g n (s.vg.gpr n) cnt post }
    else none
  | .stpFrame, s =>
    if s.vg.sp.toNat % 16 = 0 then
      let a := s.vg.sp - 16
      (s.vg.store a 8 s.x29).bind fun g =>
        (g.store (a + 8) 8 (g.gpr .x30)).map fun g => { s with vg := { g with sp := a } }
    else none
  | .movFp, s => some { s with x29 := s.vg.sp }
  | .ldrFp, s =>
    if s.vg.sp.toNat % 16 = 0 then
      (s.vg.load s.vg.sp 8).map fun x => { vg := { s.vg with sp := s.vg.sp + 16 }, x29 := x }
    else none
  | .ld4r t n post, s =>
    (ldReps s.vg (s.vg.gpr n) t 4).map fun g => { s with vg := if post then g.write .x n (s.vg.gpr n + 16) else g }
  | .cmpImm n imm, s =>
    if imm < 4096 then some { s with vg := s.vg.flagsAdd (s.vg.gpr n) (~~~(BitVec.ofNat 64 imm)) true }
    else none
  | .subsImm d n imm, s =>
    if imm < 4096 then some { s with vg := s.vg.addWithCarry .x d (s.vg.gpr n) (~~~(BitVec.ofNat 64 imm)) true }
    else none
  | .addsImm d n imm, s =>
    if imm < 4096 then some { s with vg := s.vg.addWithCarry .x d (s.vg.gpr n) (BitVec.ofNat 64 imm) false }
    else none
  | .andImm d n ones rot, s =>
    if 0 < ones ∧ ones < 64 ∧ rot < 64 then
      some { s with vg := s.vg.write .x d (s.vg.gpr n &&& bitMask ones rot) }
    else none
  | .adcZr d n, s => some { s with vg := s.vg.write .x d (s.vg.gpr n + BitVec.ofNat 64 s.vg.c.toNat) }
  | .neg d m, s => some { s with vg := s.vg.write .x d (0 - s.vg.gpr m) }
  | .movReg d m, s => some { s with vg := s.vg.write .x d (s.vg.gpr m) }
  | .ldpPost t1 t2 n imm, s =>
    if t1 ≠ t2 ∧ t1 ≠ n ∧ t2 ≠ n ∧ imm % 8 = 0 ∧ imm < 512 then
      let a := s.vg.gpr n
      (s.vg.load a 8).bind fun x => (s.vg.load (a + 8) 8).map fun y =>
        let g := (s.vg.write .x t1 (x.setWidth 64)).write .x t2 (y.setWidth 64)
        { s with vg := g.write .x n (a + BitVec.ofNat 64 imm) }
    else none
  | .ldrbReg t n m, s =>
    (s.vg.load (s.vg.gpr n + s.vg.gpr m) 1).map fun x => { s with vg := s.vg.write .w t (x.setWidth 32) }
  | .ldrbPreDec t n, s =>
    if t ≠ n then
      let a := s.vg.gpr n - 1
      (s.vg.load a 1).map fun x => { s with vg := (s.vg.write .x n a).write .w t (x.setWidth 32) }
    else none
  | .strbPostInc t n, s =>
    if t ≠ n then
      let a := s.vg.gpr n
      (s.vg.store a 1 ((s.vg.gpr t).setWidth 8)).map fun g => { s with vg := g.write .x n (a + 1) }
    else none
  | .umovB d n i, s =>
    if i < 16 then some { s with vg := s.vg.write .w d ((s.vg.v n).extractLsb' (8 * i) 8 |>.setWidth 32) }
    else none
  | .stpDPre t1 t2 imm, s =>
    if s.vg.sp.toNat % 16 = 0 ∧ imm % 16 = 0 ∧ 0 < imm ∧ imm ≤ 512 then
      let a := s.vg.sp - BitVec.ofNat 64 imm
      (stD s.vg a t1 t2).map fun g => { s with vg := { g with sp := a } }
    else none
  | .stpD t1 t2 off, s =>
    if s.vg.sp.toNat % 16 = 0 ∧ off % 8 = 0 ∧ off < 512 then
      (stD s.vg (s.vg.sp + BitVec.ofNat 64 off) t1 t2).map fun g => { s with vg := g }
    else none
  | .ldpD t1 t2 off, s =>
    if s.vg.sp.toNat % 16 = 0 ∧ off % 8 = 0 ∧ off < 512 then
      (ldD s.vg (s.vg.sp + BitVec.ofNat 64 off) t1 t2).map fun g => { s with vg := g }
    else none
  | .ldpDPost t1 t2 imm, s =>
    if s.vg.sp.toNat % 16 = 0 ∧ imm % 16 = 0 ∧ imm < 512 then
      (ldD s.vg s.vg.sp t1 t2).map fun g => { s with vg := { g with sp := s.vg.sp + BitVec.ofNat 64 imm } }
    else none

/-- The addresses an instruction accesses: VG's for its own, and for the
others each register's or doubleword's. -/
def addrs : Instr → State → List Addr
  | .vg i, s => VG.AArch64.addrs i s.vg
  | .ld1 cnt _ _ n _, s | .st1 cnt _ _ n _, s =>
    (List.range cnt).map fun j => s.vg.gpr n + BitVec.ofNat 64 (16 * j)
  | .stpFrame, s => [s.vg.sp - 16, s.vg.sp - 8]
  | .ldrFp, s => [s.vg.sp]
  | .movFp, _ => []
  | .ld4r _ n _, s => (List.range 4).map fun j => s.vg.gpr n + BitVec.ofNat 64 (4 * j)
  | .ldpPost _ _ n _, s => [s.vg.gpr n, s.vg.gpr n + 8]
  | .ldrbReg _ n m, s => [s.vg.gpr n + s.vg.gpr m]
  | .ldrbPreDec _ n, s => [s.vg.gpr n - 1]
  | .strbPostInc _ n, s => [s.vg.gpr n]
  | .stpDPre _ _ imm, s => [s.vg.sp - BitVec.ofNat 64 imm, s.vg.sp - BitVec.ofNat 64 imm + 8]
  | .stpD _ _ off, s | .ldpD _ _ off, s =>
    [s.vg.sp + BitVec.ofNat 64 off, s.vg.sp + BitVec.ofNat 64 off + 8]
  | .ldpDPost _ _ _, s => [s.vg.sp, s.vg.sp + 8]
  | .cmpImm .., _ | .subsImm .., _ | .addsImm .., _ | .andImm .., _ | .adcZr .., _ | .neg .., _
  | .movReg .., _ | .umovB .., _ => []

/-- The CPU features beyond the baseline: VG's for its own, none for the
others, which are A64 and AdvSIMD baseline instructions. -/
def Instr.requires : Instr → List String
  | .vg i => i.requires
  | _ => []

/-- The model. No program here calls or makes a frame of VG's kind, so
calls, returns, pushes and pops fault: a function's return is its `ret`,
which `layout` appends, to the return address `x30` its theorem shows it
keeps. -/
abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval
    | .vg c, s => VG.AArch64.eval c s.vg
    | .flags c, s => some (c.holds s.vg)
  call _ := none
  callAddrs _ := []
  ret _ _ := none
  retAddrs _ := []
  writesSp
    | .stpFrame | .ldrFp | .stpDPre .. | .ldpDPost .. => true
    | _ => false
  push _ _ := none
  pop _ _ _ := none
  requires := Instr.requires

/-! ## Machine code -/

/-- The `opcode` field (15–12) of LD1 and ST1 (multiple structures) for
`cnt` registers: `0111` one, `1010` two, `0110` three, `0010` four. -/
def ldstOpcode : Nat → Option Nat
  | 1 => some 0b0111
  | 2 => some 0b1010
  | 3 => some 0b0110
  | 4 => some 0b0010
  | _ => none

/-- The machine code of an instruction (DDI 0487 C6.2 and C7.2): VG's
encoding of its own (`Instr.encode`); LD1 and ST1 (multiple structures),
128-bit (`Q = 1`), `0 Q 0011000 L 000000 opcode size Rn Rt` with no offset
and `0 Q 0011001 L 0 11111 opcode size Rn Rt` post-index by the immediate,
`L` 1 for LD1; and the frame's three fixed words. -/
def Instr.encode : Instr → Option (List Nat)
  | .vg i => i.encode
  | .ld1 cnt a t n post =>
    (ldstOpcode cnt).map fun op =>
      [(if post then 0x4CDF0000 else 0x4C400000) ||| op <<< 12 ||| Enc.vsize a <<< 10 |||
        n.index <<< 5 ||| t.index]
  | .st1 cnt a t n post =>
    (ldstOpcode cnt).map fun op =>
      [(if post then 0x4C9F0000 else 0x4C000000) ||| op <<< 12 ||| Enc.vsize a <<< 10 |||
        n.index <<< 5 ||| t.index]
  -- STP (64-bit, pre-index): `10 101 0 011 0 imm7 Rt2 Rn Rt`, `imm7 = -2`.
  | .stpFrame => some [0xA9BF7BFD]
  -- ADD (immediate): `1 0 0 100010 0 imm12 Rn Rd`, `Rn = 31` (SP), `Rd = 29`.
  | .movFp => some [0x910003FD]
  -- LDR (immediate, 64-bit, post-index): `11 111 0 00 01 0 imm9 01 Rn Rt`, `imm9 = 16`.
  | .ldrFp => some [0xF84107FD]
  -- LD4R, `size = 10`, `Q = 1`: `0 Q 0011010 1 1 00000 111 0 size Rn Rt`, or
  -- post-index by the immediate, `0 Q 0011011 1 1 11111 111 0 size Rn Rt`.
  | .ld4r t n post => some [(if post then 0x4DFFE800 else 0x4D60E800) ||| n.index <<< 5 ||| t.index]
  -- SUBS (immediate), ADDS (immediate): `sf op 1 100010 0 imm12 Rn Rd`.
  | .cmpImm n imm => (Enc.addSubImm 0x71000000 .x Enc.r31 n.index imm).map ([·])
  | .subsImm d n imm => (Enc.addSubImm 0x71000000 .x d.index n.index imm).map ([·])
  | .addsImm d n imm => (Enc.addSubImm 0x31000000 .x d.index n.index imm).map ([·])
  -- AND (immediate), 64-bit: `1 00 100100 N immr imms Rn Rd`, `N = 1`.
  | .andImm d n ones rot =>
    if 0 < ones ∧ ones < 64 ∧ rot < 64 then
      some [0x92400000 ||| rot <<< 16 ||| (ones - 1) <<< 10 ||| n.index <<< 5 ||| d.index]
    else none
  -- ADC: `1 0 0 11010000 Rm 000000 Rn Rd`, `Rm = 31`.
  | .adcZr d n => some [0x9A000000 ||| Enc.rdnm d.index n.index Enc.r31]
  -- SUB (shifted register): `1 1 0 01011 00 0 Rm 000000 Rn Rd`, `Rn = 31`.
  | .neg d m => some [0xCB000000 ||| Enc.rdnm d.index Enc.r31 m.index]
  -- ORR (shifted register): `1 01 01010 00 0 Rm 000000 Rn Rd`, `Rn = 31`.
  | .movReg d m => some [0xAA000000 ||| Enc.rdnm d.index Enc.r31 m.index]
  -- LDP, 64-bit, post-index: `10 101 0 001 1 imm7 Rt2 Rn Rt`, `imm7 = imm / 8`.
  | .ldpPost t1 t2 n imm =>
    if imm % 8 = 0 ∧ imm < 512 then
      some [0xA8C00000 ||| (imm / 8) <<< 15 ||| t2.index <<< 10 ||| n.index <<< 5 ||| t1.index]
    else none
  -- LDRB (register): `00 111 0 00 01 1 Rm 011 0 10 Rn Rt`.
  | .ldrbReg t n m => some [0x38606800 ||| Enc.rdnm t.index n.index m.index]
  -- LDRB (immediate), pre-index: `00 111 0 00 01 0 imm9 11 Rn Rt`, `imm9 = -1`.
  | .ldrbPreDec t n => some [0x385FFC00 ||| n.index <<< 5 ||| t.index]
  -- STRB (immediate), post-index: `00 111 0 00 00 0 imm9 01 Rn Rt`, `imm9 = 1`.
  | .strbPostInc t n => some [0x38001400 ||| n.index <<< 5 ||| t.index]
  -- UMOV, to a 32-bit register: `0 0 0 01110000 imm5 0 0111 1 Rn Rd`, `imm5 = i:1`.
  | .umovB d n i => (Enc.imm5 .b16 i).map fun m => [0x0E003C00 ||| m <<< 16 ||| n.index <<< 5 ||| d.index]
  -- STP and LDP (SIMD&FP), 64-bit (`opc = 01`), `Rn = 31` (SP): `01 101 1 mode L
  -- imm7 Rt2 Rn Rt`, `mode` 011 pre-index, 010 signed offset, 001 post-index.
  | .stpDPre t1 t2 imm => dpair 0x6D800000 t1 t2 ((128 - imm / 8) % 128)
  | .stpD t1 t2 off => dpair 0x6D000000 t1 t2 (off / 8)
  | .ldpD t1 t2 off => dpair 0x6D400000 t1 t2 (off / 8)
  | .ldpDPost t1 t2 imm => dpair 0x6CC00000 t1 t2 (imm / 8)
where
  /-- An STP or LDP (SIMD&FP) through `sp` with `imm7`. -/
  dpair (base : Nat) (t1 t2 : VReg) (imm7 : Nat) : Option (List Nat) :=
    if imm7 < 128 then some [base ||| imm7 <<< 15 ||| t2.index <<< 10 ||| Enc.r31 <<< 5 ||| t1.index]
    else none

/-- A relocation the linker resolves in a program's machine code: the byte
offset of its instruction, its ELF type, and the symbol it names. -/
structure Reloc where
  off : Nat
  type : String
  sym : String
  deriving DecidableEq, Repr

/-- The word of a branch on `c` by `off` words from it: CBZ or CBNZ (`sf
011010 op imm19 Rt`), or B.cond (`0101010 0 imm19 0 cond`), `imm19` the
offset modulo `2 ^ 19`; `none` if it does not fit. -/
def branchWord (c : Cond) (off : Int) : Option Nat :=
  if -2 ^ 18 ≤ off ∧ off < 2 ^ 18 then
    let imm19 := (off % 2 ^ 19).toNat
    some (match c with
      | .vg (.zero sz r) => Enc.sf sz ||| 0b011010 <<< 25 ||| imm19 <<< 5 ||| r.index
      | .vg (.nonzero sz r) => Enc.sf sz ||| 0b011010 <<< 25 ||| 1 <<< 24 ||| imm19 <<< 5 ||| r.index
      | .flags cc => 0x54000000 ||| imm19 <<< 5 ||| Enc.cond cc)
  else none

/-- The word of `b` forward by `off` words (B: `000101 imm26`); `none` if it
does not fit. -/
def jumpWord (off : Nat) : Option Nat :=
  if off < 2 ^ 25 then some (0x14000000 ||| off) else none

/-- NOP (`HINT #0`), which `align` pads with. -/
def nopWord : Nat := 0xD503201F

/-- The machine code of a program from word `o` on, as rind's build emits
it, in a function that starts on a 64-byte boundary:

* each instruction's words; `adrSym`'s `adrp` and `add` with zero
  immediates and their relocations for the linker to fill (ELF for the Arm
  64-bit Architecture, `R_AARCH64_ADR_PREL_PG_HI21` and
  `R_AARCH64_ADD_ABS_LO12_NC`); and `align k`'s NOPs to the next `2 ^ k`-byte
  boundary, as `.p2align k` pads (`k` 4 to 6);
* `ite c t e` as VG's printer lowers it (`TCB/Print.lean`): the branch on
  `c` to `t`, `e`, a `b` past `t`, and `t`; or, if `t` is an empty block, the
  branch on `c` past `e`, and `e`, which the `b` would only jump to the next
  word from;
* `loop body c` as its body followed by the branch on `c` back to its first
  word.

`none` for any other control flow, which no program here has, for a branch
that does not reach, and for an instruction that does not encode. -/
def layout : Prog isa → Nat → Option (List Nat × List Reloc)
  | .block is, o =>
    is.foldlM (init := ([], [])) fun (ws, rs) i =>
      match i with
      | .vg (.adrSym d name) =>
        let at_ := o + ws.length
        some (ws ++ [0x90000000 ||| d.index, 0x91000000 ||| d.index <<< 5 ||| d.index],
          rs ++ [⟨4 * at_, "R_AARCH64_ADR_PREL_PG_HI21", name⟩,
            ⟨4 * (at_ + 1), "R_AARCH64_ADD_ABS_LO12_NC", name⟩])
      | .vg (.align k) =>
        if 4 ≤ k ∧ k ≤ 6 then
          let w := 2 ^ (k - 2)
          some (ws ++ List.replicate ((w - (o + ws.length) % w) % w) nopWord, rs)
        else none
      | i => i.encode.map fun w => (ws ++ w, rs)
  | .seq a b, o => do
    let (wa, ra) ← layout a o
    let (wb, rb) ← layout b (o + wa.length)
    return (wa ++ wb, ra ++ rb)
  | .ite c (.block []) e, o => do
    let (we, re) ← layout e (o + 1)
    let b ← branchWord c (we.length + 1 : Nat)
    return (b :: we, re)
  | .ite c t e, o => do
    let (we, re) ← layout e (o + 1)
    let (wt, rt) ← layout t (o + we.length + 2)
    let b ← branchWord c (we.length + 2 : Nat)
    let j ← jumpWord (wt.length + 1)
    return (b :: we ++ j :: wt, re ++ rt)
  | .loop body c, o => do
    let (wb, rb) ← layout body o
    let b ← branchWord c (-(wb.length : Int))
    return (wb ++ [b], rb)
  | _, _ => none

/-- The machine code of a function whose body is `c`: the body, then `ret`. -/
def function (c : Prog isa) : Option (List Nat × List Reloc) :=
  (layout c 0).map fun (ws, rs) => (ws ++ [retWord], rs)

end Rind.AArch64
